---------------------------- MODULE PermissionedBlockchain ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    Nodes,          \* finite set of permissioned nodes
    PrivKeys,       \* finite set of private keys
    PubKeys,        \* finite set of public keys
    KeyOf,          \* KeyOf[n]  : private key held by node n
    PubOf,          \* PubOf[sk] : public key corresponding to private key sk
    Hashes,         \* finite pool of precomputed hash tokens
    GenesisHash,    \* hash token bound to the genesis block
    Accounts,       \* finite set of accounts
    InitBalance,    \* genesis balance state (the only permitted minting)
    MaxAmount,      \* maximal amount of a single transfer
    MaxChanges      \* maximal number of state changes in a block

ASSUME KeyOfAssump ==
    /\ KeyOf \in [Nodes -> PrivKeys]
    /\ \A sk \in PrivKeys : \E n \in Nodes : KeyOf[n] = sk

ASSUME PubOfAssump ==
    /\ PubOf \in [PrivKeys -> PubKeys]
    /\ \A pk \in PubKeys : \E sk \in PrivKeys : PubOf[sk] = pk

ASSUME HashAssump == GenesisHash \in Hashes

ASSUME BalanceAssump ==
    /\ InitBalance \in [Accounts -> Nat]
    /\ MaxAmount \in Nat \ {0}
    /\ MaxChanges \in Nat
    /\ Nodes # {}

-----------------------------------------------------------------------------
(* Abstract cryptography *)

Sign(sk, content) == <<sk, content>>

Verify(pk, content, sig) ==
    /\ sig[1] \in PrivKeys
    /\ PubOf[sig[1]] = pk
    /\ sig[2] = content

PubKeyOfNode(n) == PubOf[KeyOf[n]]

-----------------------------------------------------------------------------
(* Blocks and state changes *)

Transfers == { t \in [from : Accounts, to : Accounts, amt : 1..MaxAmount] :
                 t.from # t.to }

ChangeSets == { S \in SUBSET Transfers : Cardinality(S) <= MaxChanges }

NoHash == CHOOSE x : x \notin Hashes

Content == Nodes \X (Hashes \cup {NoHash}) \X (SUBSET Transfers)

Block == [ creator : Nodes,
           prev    : Hashes \cup {NoHash},
           changes : SUBSET Transfers,
           sig     : PrivKeys \X Content ]

NoBlock == CHOOSE x : x \notin Block

MakeBlock(n, p, ch) ==
    [ creator |-> n,
      prev    |-> p,
      changes |-> ch,
      sig     |-> Sign(KeyOf[n], <<n, p, ch>>) ]

GenesisCreator == CHOOSE n \in Nodes : TRUE

GenesisBlock == MakeBlock(GenesisCreator, NoHash, {})

SigOK(b) == Verify(PubKeyOfNode(b.creator), <<b.creator, b.prev, b.changes>>, b.sig)

-----------------------------------------------------------------------------
(* Balances *)

RECURSIVE SetSum(_)
SetSum(S) ==
    IF S = {} THEN 0
    ELSE LET t == CHOOSE x \in S : TRUE
         IN  t.amt + SetSum(S \ {t})

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET a == CHOOSE x \in S : TRUE
         IN  f[a] + SumOver(f, S \ {a})

TotalFunds == SumOver(InitBalance, Accounts)

Apply(bal, ch) ==
    [ a \in Accounts |->
        (bal[a] + SetSum({ t \in ch : t.to = a }))
          - SetSum({ t \in ch : t.from = a }) ]

NonNeg(bal) == \A a \in Accounts : bal[a] >= 0

-----------------------------------------------------------------------------
VARIABLES
    hashMap,    \* hashMap[h] : NoBlock or the concrete block bound to token h
    ledger,     \* ledger[n]  : set of block hashes in n's local ledger (tree, forks allowed)
    msgs        \* set of disseminated blocks [hash, block]

vars == <<hashMap, ledger, msgs>>

RECURSIVE BalanceAt(_)
BalanceAt(h) ==
    IF h = GenesisHash THEN InitBalance
    ELSE Apply(BalanceAt(hashMap[h].prev), hashMap[h].changes)

Bound       == { h \in Hashes : hashMap[h] # NoBlock }
Unused      == Hashes \ Bound
Exhausted   == Unused = {}
BoundBlocks == { hashMap[h] : h \in Bound }

ValidExtension(p, b) ==
    /\ p \in Bound
    /\ b.prev = p
    /\ SigOK(b)
    /\ NonNeg(Apply(BalanceAt(p), b.changes))

-----------------------------------------------------------------------------
Init ==
    /\ hashMap = [ h \in Hashes |-> IF h = GenesisHash THEN GenesisBlock ELSE NoBlock ]
    /\ ledger  = [ n \in Nodes |-> {GenesisHash} ]
    /\ msgs    = {}

\* Node n creates a block extending p, signs it, and consumes an unused hash token h.
Propose(n, p, ch, h) ==
    /\ p \in ledger[n]
    /\ h \in Unused
    /\ LET b == MakeBlock(n, p, ch) IN
        /\ b \notin BoundBlocks
        /\ ValidExtension(p, b)
        /\ hashMap' = [hashMap EXCEPT ![h] = b]
        /\ ledger'  = [ledger EXCEPT ![n] = @ \cup {h}]
        /\ msgs'    = msgs \cup { [hash |-> h, block |-> b] }

\* Node n receives a disseminated block and adopts it if valid and it extends its view.
Receive(n, m) ==
    /\ m \in msgs
    /\ m.hash \notin ledger[n]
    /\ hashMap[m.hash] = m.block
    /\ m.block.prev \in ledger[n]
    /\ ValidExtension(m.block.prev, m.block)
    /\ ledger' = [ledger EXCEPT ![n] = @ \cup {m.hash}]
    /\ UNCHANGED <<hashMap, msgs>>

ProposeAny ==
    /\ ~Exhausted
    /\ \E n \in Nodes, ch \in ChangeSets, h \in Hashes :
          \E p \in ledger[n] : Propose(n, p, ch, h)

ReceiveAny(n) ==
    /\ ~Exhausted
    /\ \E m \in msgs : Receive(n, m)

\* When all hash tokens are consumed the system only stutters.
Stutter ==
    /\ Exhausted
    /\ UNCHANGED vars

Next ==
    \/ ProposeAny
    \/ \E n \in Nodes : ReceiveAny(n)
    \/ Stutter

Fairness ==
    /\ WF_vars(ProposeAny)
    /\ \A n \in Nodes : WF_vars(ReceiveAny(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ hashMap \in [Hashes -> Block \cup {NoBlock}]
    /\ ledger \in [Nodes -> SUBSET Hashes]
    /\ msgs \subseteq [hash : Hashes, block : Block]
    /\ \A n \in Nodes : GenesisHash \in ledger[n]

\* No two different hash tokens represent the same block; each token binds one block.
HashIntegrity ==
    /\ hashMap[GenesisHash] = GenesisBlock
    /\ \A h1, h2 \in Bound : hashMap[h1] = hashMap[h2] => h1 = h2

\* Messages never invent or reuse hash tokens.
MessagesConsistent ==
    \A m \in msgs : m.hash \in Bound /\ hashMap[m.hash] = m.block

\* Ledgers contain only bound hashes and are closed under the prev pointer.
LedgerWellFormed ==
    \A n \in Nodes : \A h \in ledger[n] :
        /\ h \in Bound
        /\ h # GenesisHash => hashMap[h].prev \in ledger[n]

\* Every block's signature verifies against the creator's public key.
SignatureCorrectness ==
    \A h \in Bound : SigOK(hashMap[h])

\* No invalid block is ever accepted into any ledger.
NoInvalidBlocks ==
    \A n \in Nodes : \A h \in ledger[n] \ {GenesisHash} :
        ValidExtension(hashMap[h].prev, hashMap[h])

\* Balances are nonnegative and total funds are conserved (minting only in genesis).
BalanceSafety ==
    \A h \in Bound :
        /\ NonNeg(BalanceAt(h))
        /\ SumOver(BalanceAt(h), Accounts) = TotalFunds

Invariants ==
    /\ TypeOK
    /\ HashIntegrity
    /\ MessagesConsistent
    /\ LedgerWellFormed
    /\ SignatureCorrectness
    /\ NoInvalidBlocks
    /\ BalanceSafety

(* Action properties *)

\* Once a token is bound to a block it never changes or reverts to NoBlock.
HashPermanence ==
    [][ \A h \in Hashes :
          hashMap[h] # NoBlock => hashMap'[h] = hashMap[h] ]_vars

\* When hash tokens are exhausted, ledgers and hashes no longer change.
ExhaustionStutter ==
    [][ Exhausted => UNCHANGED <<ledger, hashMap>> ]_vars

\* Ledgers only grow.
LedgerMonotonic ==
    [][ \A n \in Nodes : ledger[n] \subseteq ledger'[n] ]_vars

-----------------------------------------------------------------------------
(* Liveness (optional to model-check) *)

\* If unused hashes remain, eventually a new block is appended to some ledger.
Progress ==
    \A k \in 0..Cardinality(Hashes) :
        (~Exhausted /\ Cardinality(Bound) = k) ~> (Cardinality(Bound) > k)

\* Reliable delivery: every disseminated block eventually reaches every node
\* (or the system has exhausted its hash pool).
EventualDelivery ==
    \A h \in Hashes : \A n \in Nodes :
        (\E m \in msgs : m.hash = h) ~> (h \in ledger[n] \/ Exhausted)

=============================================================================