------------------------------- MODULE Nano -------------------------------
(***************************************************************************)
(* A specification of the Nano cryptocurrency protocol (block-lattice).   *)
(* Each account owns its own chain of blocks. Blocks are signed with the  *)
(* account's private key and are linked by hashes. Nodes keep their own   *)
(* copy of the ledger, receive blocks asynchronously, validate them and   *)
(* add them to their local view. Hashing is modelled as a global          *)
(* injective assignment of fresh hash values to signed blocks, so that    *)
(* every node sees the same hash for the same block.                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash,               \* Set of possible hash values
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys (account identifiers)
    KeyPair,            \* Function mapping private keys to public keys
    Node,               \* Set of network nodes
    GenesisBalance,     \* Total amount of currency created at genesis
    GenesisPrivateKey,  \* Private key controlling the genesis account
    NoBlock             \* Marker value: no block stored under a hash

ASSUME HashAssumption == IsFiniteSet(Hash) /\ Hash # {}
ASSUME KeyPairAssumption ==
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ \A k1, k2 \in PrivateKey : KeyPair[k1] = KeyPair[k2] => k1 = k2
    /\ \A pub \in PublicKey : \E priv \in PrivateKey : KeyPair[priv] = pub
ASSUME NodeAssumption == Node # {}
ASSUME BalanceAssumption == GenesisBalance \in Nat \ {0}
ASSUME GenesisKeyAssumption == GenesisPrivateKey \in PrivateKey

VARIABLES
    hashFunction,       \* Global hash assignment: Hash -> SignedBlock or NoBlock
    distributedLedger,  \* Each node's view of the ledger: Node -> (Hash -> SignedBlock or NoBlock)
    received            \* Blocks each node has received from the network

vars == <<hashFunction, distributedLedger, received>>

-----------------------------------------------------------------------------
(* Block structure *)

Balance == 0 .. GenesisBalance

GenesisBlockType ==
    [type : {"genesis"}, account : PublicKey, balance : {GenesisBalance}]

SendBlockType ==
    [type : {"send"}, previous : Hash, destination : PublicKey, balance : Balance]

OpenBlockType ==
    [type : {"open"}, account : PublicKey, source : Hash]

ReceiveBlockType ==
    [type : {"receive"}, previous : Hash, source : Hash]

Block == GenesisBlockType \cup SendBlockType \cup OpenBlockType \cup ReceiveBlockType

Signature == [data : Block, signedWith : PrivateKey]

SignedBlock == [block : Block, signature : Signature]

ASSUME NoBlockAssumption == NoBlock \notin SignedBlock

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(* Abstract cryptography: a signature records the signed data and key.    *)
Sign(data, priv) == [data |-> data, signedWith |-> priv]

ValidSignature(pub, data, sig) ==
    /\ sig.data = data
    /\ KeyPair[sig.signedWith] = pub

SignBlock(b, priv) == [block |-> b, signature |-> Sign(b, priv)]

-----------------------------------------------------------------------------
(* Genesis *)

GenesisAccount == KeyPair[GenesisPrivateKey]

GenesisBlock ==
    SignBlock([type    |-> "genesis",
               account |-> GenesisAccount,
               balance |-> GenesisBalance], GenesisPrivateKey)

GenesisHash == CHOOSE h \in Hash : TRUE

GenesisLedger == [h \in Hash |-> IF h = GenesisHash THEN GenesisBlock ELSE NoBlock]

-----------------------------------------------------------------------------
(* Ledger query operators *)

InLedger(L) == {h \in Hash : L[h] # NoBlock}

HasPrevious(L, h) == L[h].block.type \in {"send", "receive"}

HasSource(L, h) == L[h].block.type \in {"open", "receive"}

RECURSIVE BlockAccount(_, _)
BlockAccount(L, h) ==
    LET b == L[h].block IN
    IF b.type \in {"genesis", "open"}
    THEN b.account
    ELSE BlockAccount(L, b.previous)

RECURSIVE BalanceAt(_, _), SendAmount(_, _)
BalanceAt(L, h) ==
    LET b == L[h].block IN
    CASE b.type = "genesis" -> b.balance
      [] b.type = "send"    -> b.balance
      [] b.type = "open"    -> SendAmount(L, b.source)
      [] b.type = "receive" -> BalanceAt(L, b.previous) + SendAmount(L, b.source)

SendAmount(L, h) == BalanceAt(L, L[h].block.previous) - L[h].block.balance

IsOpen(L, pub) ==
    \E h \in InLedger(L) :
        /\ L[h].block.type \in {"genesis", "open"}
        /\ L[h].block.account = pub

HasSuccessor(L, h) ==
    \E h2 \in InLedger(L) : HasPrevious(L, h2) /\ L[h2].block.previous = h

IsFrontier(L, pub, h) ==
    /\ h \in InLedger(L)
    /\ BlockAccount(L, h) = pub
    /\ ~HasSuccessor(L, h)

Frontier(L, pub) == CHOOSE h \in Hash : IsFrontier(L, pub, h)

Consumed(L, h) ==
    \E h2 \in InLedger(L) : HasSource(L, h2) /\ L[h2].block.source = h

PendingSends(L) ==
    {h \in InLedger(L) : L[h].block.type = "send" /\ ~Consumed(L, h)}

IsPendingFor(L, h, pub) ==
    /\ h \in PendingSends(L)
    /\ L[h].block.destination = pub

AccountBalance(L, pub) ==
    IF IsOpen(L, pub) THEN BalanceAt(L, Frontier(L, pub)) ELSE 0

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE IN f[x] + SumOver(f, S \ {x})

(* Set of hashes reachable from S by following previous links in k steps *)
PrevStep(L, S) ==
    {L[h].block.previous : h \in {x \in S : L[x] # NoBlock /\ HasPrevious(L, x)}}

RECURSIVE Reachable(_, _, _)
Reachable(L, S, k) ==
    IF k = 0 THEN S ELSE Reachable(L, S \cup PrevStep(L, S), k - 1)

-----------------------------------------------------------------------------
(* Block validation, as performed by every node before accepting a block *)

ValidBlock(L, sb) ==
    LET b   == sb.block
        sig == sb.signature
    IN
    /\ sig.data = b
    /\ CASE b.type = "genesis" -> FALSE
         [] b.type = "send" ->
                (/\ b.previous \in InLedger(L)
                 /\ ~HasSuccessor(L, b.previous)
                 /\ ValidSignature(BlockAccount(L, b.previous), b, sig)
                 /\ b.balance < BalanceAt(L, b.previous))
         [] b.type = "open" ->
                (/\ ~IsOpen(L, b.account)
                 /\ IsPendingFor(L, b.source, b.account)
                 /\ ValidSignature(b.account, b, sig))
         [] b.type = "receive" ->
                (/\ b.previous \in InLedger(L)
                 /\ ~HasSuccessor(L, b.previous)
                 /\ IsPendingFor(L, b.source, BlockAccount(L, b.previous))
                 /\ ValidSignature(BlockAccount(L, b.previous), b, sig))

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ hashFunction = GenesisLedger
    /\ distributedLedger = [n \in Node |-> GenesisLedger]
    /\ received = [n \in Node |-> {GenesisBlock}]

-----------------------------------------------------------------------------
(* Actions *)

(* Compute the hash of a newly created signed block (assign a fresh hash  *)
(* if it has never been hashed before) and hand it to the creating node.  *)
PublishBlock(n, b, priv) ==
    LET sb == SignBlock(b, priv) IN
    /\ sb \notin received[n]
    /\ \/ /\ \E h \in Hash : hashFunction[h] = sb
          /\ UNCHANGED hashFunction
       \/ /\ ~\E h \in Hash : hashFunction[h] = sb
          /\ \E h \in Hash :
                /\ hashFunction[h] = NoBlock
                /\ hashFunction' = [hashFunction EXCEPT ![h] = sb]
    /\ received' = [received EXCEPT ![n] = @ \cup {sb}]
    /\ UNCHANGED distributedLedger

(* Holder of priv creates a send block on its chain, based on node n's view *)
CreateSend(n, priv, dest, newBalance) ==
    LET L   == distributedLedger[n]
        pub == KeyPair[priv]
    IN
    /\ IsOpen(L, pub)
    /\ LET prev == Frontier(L, pub) IN
       /\ newBalance < BalanceAt(L, prev)
       /\ PublishBlock(n, [type        |-> "send",
                           previous    |-> prev,
                           destination |-> dest,
                           balance     |-> newBalance], priv)

(* Holder of priv opens its account by claiming a pending send *)
CreateOpen(n, priv, src) ==
    LET L   == distributedLedger[n]
        pub == KeyPair[priv]
    IN
    /\ ~IsOpen(L, pub)
    /\ IsPendingFor(L, src, pub)
    /\ PublishBlock(n, [type    |-> "open",
                        account |-> pub,
                        source  |-> src], priv)

(* Holder of priv claims a pending send on its already-open chain *)
CreateReceive(n, priv, src) ==
    LET L   == distributedLedger[n]
        pub == KeyPair[priv]
    IN
    /\ IsOpen(L, pub)
    /\ IsPendingFor(L, src, pub)
    /\ PublishBlock(n, [type     |-> "receive",
                        previous |-> Frontier(L, pub),
                        source   |-> src], priv)

(* A node validates a received block and adds it to its ledger *)
ProcessBlock(n, h) ==
    LET sb == hashFunction[h] IN
    /\ sb # NoBlock
    /\ sb \in received[n]
    /\ distributedLedger[n][h] = NoBlock
    /\ ValidBlock(distributedLedger[n], sb)
    /\ distributedLedger' = [distributedLedger EXCEPT ![n][h] = sb]
    /\ UNCHANGED <<hashFunction, received>>

(* A node broadcasts a block from its ledger to another node (async) *)
BroadcastBlock(n, m, h) ==
    /\ n # m
    /\ distributedLedger[n][h] # NoBlock
    /\ distributedLedger[n][h] \notin received[m]
    /\ received' = [received EXCEPT ![m] = @ \cup {distributedLedger[n][h]}]
    /\ UNCHANGED <<hashFunction, distributedLedger>>

Next ==
    \/ \E n \in Node, priv \in PrivateKey, dest \in PublicKey, bal \in Balance :
          CreateSend(n, priv, dest, bal)
    \/ \E n \in Node, priv \in PrivateKey, src \in Hash : CreateOpen(n, priv, src)
    \/ \E n \in Node, priv \in PrivateKey, src \in Hash : CreateReceive(n, priv, src)
    \/ \E n \in Node, h \in Hash : ProcessBlock(n, h)
    \/ \E n, m \in Node, h \in Hash : BroadcastBlock(n, m, h)

Fairness ==
    /\ \A n, m \in Node, h \in Hash : WF_vars(BroadcastBlock(n, m, h))
    /\ \A n \in Node, h \in Hash : WF_vars(ProcessBlock(n, h))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeInvariant ==
    /\ hashFunction \in Ledger
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

(* Hashes are injective: distinct hashes identify distinct blocks *)
HashUniqueness ==
    \A h1, h2 \in Hash :
        (hashFunction[h1] # NoBlock /\ hashFunction[h1] = hashFunction[h2]) => h1 = h2

(* All nodes agree with the global hash assignment *)
LedgerConsistency ==
    \A n \in Node, h \in Hash :
        distributedLedger[n][h] # NoBlock => distributedLedger[n][h] = hashFunction[h]

(* Every block reference points to an existing block of the right kind,   *)
(* and following previous links never produces a cycle.                   *)
ChainIntegrity ==
    \A n \in Node :
        LET L == distributedLedger[n] IN
        /\ L[GenesisHash] = GenesisBlock
        /\ \A h \in InLedger(L) :
              /\ HasPrevious(L, h) => L[h].block.previous \in InLedger(L)
              /\ HasSource(L, h) =>
                    /\ L[h].block.source \in InLedger(L)
                    /\ L[L[h].block.source].block.type = "send"
              /\ h \notin Reachable(L, PrevStep(L, {h}), Cardinality(Hash))
        /\ \A h \in InLedger(L) :
              L[h].block.type = "genesis" => h = GenesisHash

(* Only the holder of an account's private key creates its blocks *)
Ownership ==
    \A n \in Node :
        LET L == distributedLedger[n] IN
        \A h \in InLedger(L) :
            /\ L[h].signature.data = L[h].block
            /\ KeyPair[L[h].signature.signedWith] = BlockAccount(L, h)

(* No account spends more than it has; no forks; sends claimed at most once *)
NoDoubleSpend ==
    \A n \in Node :
        LET L == distributedLedger[n] IN
        /\ \A h \in InLedger(L) :
              L[h].block.type = "send" =>
                  L[h].block.balance < BalanceAt(L, L[h].block.previous)
        /\ \A h1, h2 \in InLedger(L) :
              /\ (h1 # h2 /\ HasPrevious(L, h1) /\ HasPrevious(L, h2))
                    => L[h1].block.previous # L[h2].block.previous
              /\ (h1 # h2 /\ HasSource(L, h1) /\ HasSource(L, h2))
                    => L[h1].block.source # L[h2].block.source
              /\ (h1 # h2 /\ L[h1].block.type \in {"genesis", "open"}
                          /\ L[h2].block.type \in {"genesis", "open"})
                    => L[h1].block.account # L[h2].block.account
              /\ (L[h1].block.type = "open" /\ L[h2].block.type = "send"
                          /\ L[h1].block.source = h2)
                    => L[h2].block.destination = L[h1].block.account
              /\ (L[h1].block.type = "receive" /\ L[h2].block.type = "send"
                          /\ L[h1].block.source = h2)
                    => L[h2].block.destination = BlockAccount(L, h1)

(* Total value (account balances plus in-flight sends) is constant *)
ConservationOfFunds ==
    \A n \in Node :
        LET L == distributedLedger[n] IN
        SumOver([p \in PublicKey |-> AccountBalance(L, p)], PublicKey)
          + SumOver([h \in PendingSends(L) |-> SendAmount(L, h)], PendingSends(L))
          = GenesisBalance

SafetyInvariant ==
    /\ TypeInvariant
    /\ HashUniqueness
    /\ LedgerConsistency
    /\ ChainIntegrity
    /\ Ownership
    /\ NoDoubleSpend
    /\ ConservationOfFunds

-----------------------------------------------------------------------------
(* Liveness: every block in some node's ledger eventually reaches every   *)
(* other node.                                                            *)

BlockPropagation ==
    \A n, m \in Node, h \in Hash :
        (distributedLedger[n][h] # NoBlock)
            ~> (hashFunction[h] \in received[m] \/ distributedLedger[m][h] # NoBlock)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => BlockPropagation

=============================================================================