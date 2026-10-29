------------------------------- MODULE MCNano -------------------------------
(***************************************************************************)
(* Model-checking adaptation of the Nano block-lattice specification.     *)
(* The abstract hash calculation of Nano is replaced by a model-level     *)
(* hash function state (hashFunction) that assigns each newly seen block   *)
(* to a previously unused element of the finite set Hash. Once all hashes  *)
(* are used up, the system stutters gracefully instead of deadlocking.     *)
(* The underlying Nano behaviour is inlined below so that this module is   *)
(* self-contained.                                                         *)
(***************************************************************************)
EXTENDS
    Naturals,
    FiniteSets

CONSTANTS
    Hash,
    NoHashVal,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance,
    NoBlockVal

ASSUME
    /\ Cardinality(Hash) > 0
    /\ NoHashVal \notin Hash
    /\ Cardinality(PrivateKey) = Cardinality(PublicKey)
    /\ Cardinality(PrivateKey) > 0
    /\ Node # {}
    /\ GenesisBalance \in Nat \ {0}

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

Vars == <<hashFunction, lastHash, distributedLedger, received>>

\* View used by TLC: ignore hashFunction and lastHash when hashing states.
View == <<distributedLedger, received>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Underlying Nano definitions                                             *)
(***************************************************************************)

KeyPair ==
    CHOOSE mapping \in [PrivateKey -> PublicKey] :
        \A k1, k2 \in PrivateKey : mapping[k1] = mapping[k2] => k1 = k2

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type : {"genesis"}, account : PublicKey, balance : {GenesisBalance}]

SendBlock ==
    [type : {"send"}, previous : Hash, balance : AccountBalance, link : PublicKey]

OpenBlock ==
    [type : {"open"}, account : PublicKey, link : Hash, rep : PublicKey]

ReceiveBlock ==
    [type : {"receive"}, previous : Hash, link : Hash]

ChangeRepBlock ==
    [type : {"change"}, previous : Hash, rep : PublicKey]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

Signature == [data : Hash, signedWith : PrivateKey]

SignedBlock == [block : Block, signature : Signature]

Ledger == [Hash -> SignedBlock \cup {NoBlockVal}]

Sign(hash, privateKey) == [data |-> hash, signedWith |-> privateKey]

SignerOf(signedBlock) == KeyPair[signedBlock.signature.signedWith]

Exists(ledger, hash) == ledger[hash] # NoBlockVal

HasPrevious(b) == b.type \in {"send", "receive", "change"}

HasSourceLink(b) == b.type \in {"open", "receive"}

RECURSIVE AccountOf(_, _)
AccountOf(ledger, hash) ==
    LET b == ledger[hash].block IN
    IF b.type \in {"genesis", "open"}
    THEN b.account
    ELSE AccountOf(ledger, b.previous)

RECURSIVE BalanceAt(_, _), SendValue(_, _)
BalanceAt(ledger, hash) ==
    LET b == ledger[hash].block IN
    CASE b.type = "genesis" -> b.balance
      [] b.type = "send"    -> b.balance
      [] b.type = "open"    -> SendValue(ledger, b.link)
      [] b.type = "receive" -> BalanceAt(ledger, b.previous) + SendValue(ledger, b.link)
      [] b.type = "change"  -> BalanceAt(ledger, b.previous)

SendValue(ledger, hash) ==
    LET b == ledger[hash].block IN
    BalanceAt(ledger, b.previous) - b.balance

IsFrontier(ledger, hash) ==
    ~\E h \in Hash :
        /\ Exists(ledger, h)
        /\ HasPrevious(ledger[h].block)
        /\ ledger[h].block.previous = hash

IsAccountOpen(ledger, publicKey) ==
    \E h \in Hash :
        /\ Exists(ledger, h)
        /\ ledger[h].block.type \in {"genesis", "open"}
        /\ ledger[h].block.account = publicKey

IsUnreceivedSendTo(ledger, hash, publicKey) ==
    /\ Exists(ledger, hash)
    /\ ledger[hash].block.type = "send"
    /\ ledger[hash].block.link = publicKey
    /\ ~\E h \in Hash :
            /\ Exists(ledger, h)
            /\ HasSourceLink(ledger[h].block)
            /\ ledger[h].block.link = hash

LedgerEmpty(ledger) == \A h \in Hash : ~Exists(ledger, h)

ValidBlock(ledger, block, signer) ==
    CASE block.type = "genesis" ->
            /\ LedgerEmpty(ledger)
            /\ signer = block.account
      [] block.type = "send" ->
            /\ Exists(ledger, block.previous)
            /\ IsFrontier(ledger, block.previous)
            /\ signer = AccountOf(ledger, block.previous)
            /\ block.balance < BalanceAt(ledger, block.previous)
      [] block.type = "open" ->
            /\ signer = block.account
            /\ ~IsAccountOpen(ledger, block.account)
            /\ IsUnreceivedSendTo(ledger, block.link, block.account)
      [] block.type = "receive" ->
            /\ Exists(ledger, block.previous)
            /\ IsFrontier(ledger, block.previous)
            /\ signer = AccountOf(ledger, block.previous)
            /\ IsUnreceivedSendTo(ledger, block.link, AccountOf(ledger, block.previous))
      [] block.type = "change" ->
            /\ Exists(ledger, block.previous)
            /\ IsFrontier(ledger, block.previous)
            /\ signer = AccountOf(ledger, block.previous)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-level hash function implementation                                *)
(***************************************************************************)

UndefinedHashesExist ==
    \E hash \in Hash : hashFunction[hash] = NoBlockVal

HashOf(block) ==
    IF \E hash \in Hash : hashFunction[hash] = block
    THEN CHOOSE hash \in Hash : hashFunction[hash] = block
    ELSE CHOOSE hash \in Hash : hashFunction[hash] = NoBlockVal

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    LET hash == HashOf(block) IN
    /\ newLastHash = hash
    /\ hashFunction' = [hashFunction EXCEPT ![hash] = block]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Nano actions                                                            *)
(***************************************************************************)

NanoInit ==
    /\ lastHash = NoHashVal
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privateKey) ==
    LET block == [type |-> "genesis",
                  account |-> KeyPair[privateKey],
                  balance |-> GenesisBalance] IN
    /\ lastHash = NoHashVal
    /\ CalculateHashImpl(block, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |->
            [distributedLedger[n] EXCEPT
                ![lastHash'] = [block |-> block,
                                signature |-> Sign(lastHash', privateKey)]]]
    /\ UNCHANGED received

CreateBlock(node, privateKey) ==
    LET ledger == distributedLedger[node] IN
    \E block \in SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock :
        /\ ValidBlock(ledger, block, KeyPair[privateKey])
        /\ CalculateHashImpl(block, lastHash, lastHash')
        /\ received' =
            [n \in Node |->
                received[n] \cup {[block |-> block,
                                   signature |-> Sign(lastHash', privateKey)]}]
        /\ UNCHANGED distributedLedger

ProcessBlock(node) ==
    LET ledger == distributedLedger[node] IN
    \E sb \in received[node] :
        LET hash == sb.signature.data IN
        /\ ~Exists(ledger, hash)
        /\ hashFunction[hash] = sb.block
        /\ ValidBlock(ledger, sb.block, SignerOf(sb))
        /\ distributedLedger' =
            [distributedLedger EXCEPT ![node][hash] = sb]
        /\ UNCHANGED <<hashFunction, lastHash, received>>

NanoNext ==
    \/ \E privateKey \in PrivateKey : CreateGenesisBlock(privateKey)
    \/ \E node \in Node, privateKey \in PrivateKey : CreateBlock(node, privateKey)
    \/ \E node \in Node : ProcessBlock(node)

NanoTypeInvariant ==
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicallySecure ==
    \A n \in Node, h \in Hash :
        LET ledger == distributedLedger[n] IN
        Exists(ledger, h) =>
            /\ ledger[h].signature.data = h
            /\ SignerOf(ledger[h]) = AccountOf(ledger, h)

LedgersConsistent ==
    \A n1, n2 \in Node, h \in Hash :
        (Exists(distributedLedger[n1], h) /\ Exists(distributedLedger[n2], h))
            => distributedLedger[n1][h] = distributedLedger[n2][h]

NoForks ==
    \A n \in Node, h1, h2 \in Hash :
        LET ledger == distributedLedger[n] IN
        ( /\ h1 # h2
          /\ Exists(ledger, h1) /\ Exists(ledger, h2)
          /\ HasPrevious(ledger[h1].block)
          /\ HasPrevious(ledger[h2].block) )
            => ledger[h1].block.previous # ledger[h2].block.previous

NoDoubleReceive ==
    \A n \in Node, h1, h2 \in Hash :
        LET ledger == distributedLedger[n] IN
        ( /\ h1 # h2
          /\ Exists(ledger, h1) /\ Exists(ledger, h2)
          /\ HasSourceLink(ledger[h1].block)
          /\ HasSourceLink(ledger[h2].block) )
            => ledger[h1].block.link # ledger[h2].block.link

BalancesValid ==
    \A n \in Node, h \in Hash :
        Exists(distributedLedger[n], h) =>
            BalanceAt(distributedLedger[n], h) \in AccountBalance

SafetyInvariant ==
    /\ CryptographicallySecure
    /\ LedgersConsistent
    /\ NoForks
    /\ NoDoubleReceive
    /\ BalancesValid

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking specification                                            *)
(***************************************************************************)

MCTypeInvariant ==
    /\ hashFunction \in [Hash -> Block \cup {NoBlockVal}]
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ NanoTypeInvariant

MCInit ==
    /\ hashFunction = [hash \in Hash |-> NoBlockVal]
    /\ NanoInit

StutterWhenHashesDepleted ==
    /\ UNCHANGED hashFunction
    /\ UNCHANGED lastHash
    /\ UNCHANGED distributedLedger
    /\ UNCHANGED received

MCNext ==
    IF UndefinedHashesExist
    THEN NanoNext
    ELSE StutterWhenHashesDepleted

Init == MCInit

Next == MCNext

MCSpec ==
    /\ MCInit
    /\ [][MCNext]_Vars

Spec == MCSpec

MCSafetyInvariant == MCTypeInvariant /\ SafetyInvariant

THEOREM MCSafety == MCSpec => [](MCTypeInvariant /\ SafetyInvariant)

=============================================================================