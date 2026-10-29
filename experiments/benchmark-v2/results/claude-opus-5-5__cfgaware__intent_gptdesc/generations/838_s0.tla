---------------------------- MODULE Blockchain ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,                    \* finite set of nodes
    PrivateKey,              \* finite set of private keys
    PublicKey,               \* finite set of public keys
    Hash,                    \* finite pool of precomputed hash tokens
    CalculateHash(_, _, _),  \* hash "function" (prev, transfer, creator)
    GenesisBalance,          \* [Node -> Nat] initial balances
    NoHash,                  \* "no previous block" (genesis pointer)
    NoBlock                  \* "hash token not yet bound to a block"

VARIABLES
    hashes,   \* [Hash -> Block \cup {NoBlock}] binding of tokens to blocks
    ledger    \* [Node -> SUBSET Hash] each node's local copy of the ledger

vars == <<hashes, ledger>>

-----------------------------------------------------------------------------
(* Default values usable for the sentinel constants                       *)
-----------------------------------------------------------------------------
NoHashVal == "NoHash"
NoBlockVal == [none |-> TRUE]

-----------------------------------------------------------------------------
(* Keys: every node has a private key, every private key has a public key *)
(* Prefer surjective mappings when they exist; keys need not be 1-1.      *)
-----------------------------------------------------------------------------
PrivOf ==
    IF \E f \in [Node -> PrivateKey] : \A k \in PrivateKey : \E n \in Node : f[n] = k
    THEN CHOOSE f \in [Node -> PrivateKey] : \A k \in PrivateKey : \E n \in Node : f[n] = k
    ELSE CHOOSE f \in [Node -> PrivateKey] : TRUE

PubOf ==
    IF \E f \in [PrivateKey -> PublicKey] : \A k \in PublicKey : \E p \in PrivateKey : f[p] = k
    THEN CHOOSE f \in [PrivateKey -> PublicKey] : \A k \in PublicKey : \E p \in PrivateKey : f[p] = k
    ELSE CHOOSE f \in [PrivateKey -> PublicKey] : TRUE

Sign(n) == PrivOf[n]

VerifySig(b) == /\ b.sig \in PrivateKey
                /\ PubOf[b.sig] = PubOf[PrivOf[b.creator]]

-----------------------------------------------------------------------------
(* Funds and blocks                                                       *)
-----------------------------------------------------------------------------
RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TotalFunds == SumOver(GenesisBalance, Node)

Transfer == [from : Node, to : Node, amount : 1..TotalFunds]

Block == [prev : Hash \cup {NoHash}, creator : Node, tx : Transfer, sig : PrivateKey]

MakeBlock(prev, t, n) == [prev |-> prev, creator |-> n, tx |-> t, sig |-> Sign(n)]

Used(h) == hashes[h] # NoBlock

UnusedHashes == {h \in Hash : ~Used(h)}

HashesRemain == UnusedHashes # {}

Apply(bal, t) ==
    [bal EXCEPT ![t.from] = @ - t.amount, ![t.to] = @ + t.amount]

\* Balance state after the chain ending at h (NoHash = genesis state).
RECURSIVE BalanceAt(_)
BalanceAt(h) ==
    IF h = NoHash THEN GenesisBalance
    ELSE Apply(BalanceAt(hashes[h].prev), hashes[h].tx)

ValidTransfer(prev, t, n) ==
    /\ t.from = n
    /\ t.amount <= BalanceAt(prev)[t.from]

ValidBlock(b) ==
    /\ b \in Block
    /\ VerifySig(b)
    /\ (b.prev = NoHash \/ Used(b.prev))
    /\ ValidTransfer(b.prev, b.tx, b.creator)

-----------------------------------------------------------------------------
(* Hash implementation: identical content yields its existing token;      *)
(* otherwise an unused token is consumed; NoHash if pool exhausted.       *)
-----------------------------------------------------------------------------
CalculateHashImpl(prev, t, n) ==
    LET b == MakeBlock(prev, t, n) IN
    IF \E h \in Hash : hashes[h] = b
        THEN CHOOSE h \in Hash : hashes[h] = b
    ELSE IF HashesRemain
        THEN CHOOSE h \in UnusedHashes : TRUE
    ELSE NoHash

-----------------------------------------------------------------------------
(* Behavior                                                               *)
-----------------------------------------------------------------------------
Init ==
    /\ hashes = [h \in Hash |-> NoBlock]
    /\ ledger = [n \in Node |-> {}]

\* Node n creates, signs and appends a block extending a block it knows.
Propose(n, prev, t) ==
    /\ HashesRemain
    /\ prev \in ledger[n] \cup {NoHash}
    /\ ValidTransfer(prev, t, n)
    /\ LET b == MakeBlock(prev, t, n)
           h == CalculateHash(prev, t, n)
       IN /\ h \in Hash
          /\ hashes[h] = NoBlock
          /\ ValidBlock(b)
          /\ hashes' = [hashes EXCEPT ![h] = b]
          /\ ledger' = [ledger EXCEPT ![n] = @ \cup {h}]

\* Node n adopts a block created by someone else (forks allowed).
Receive(n, h) ==
    /\ HashesRemain
    /\ Used(h)
    /\ h \notin ledger[n]
    /\ hashes[h].prev \in ledger[n] \cup {NoHash}
    /\ ValidBlock(hashes[h])
    /\ ledger' = [ledger EXCEPT ![n] = @ \cup {h}]
    /\ UNCHANGED hashes

\* Once the hash pool is exhausted the system only stutters.
Exhausted ==
    /\ ~HashesRemain
    /\ UNCHANGED vars

ProposeStep ==
    \E n \in Node, prev \in Hash \cup {NoHash}, t \in Transfer : Propose(n, prev, t)

ReceiveStep == \E n \in Node, h \in Hash : Receive(n, h)

Next == ProposeStep \/ ReceiveStep \/ Exhausted

Spec == Init /\ [][Next]_vars /\ WF_vars(ProposeStep) /\ WF_vars(ReceiveStep)

View == <<hashes, ledger>>

-----------------------------------------------------------------------------
(* Properties                                                             *)
-----------------------------------------------------------------------------
TypeInvariant ==
    /\ hashes \in [Hash -> Block \cup {NoBlock}]
    /\ ledger \in [Node -> SUBSET Hash]
    /\ \A n \in Node : \A h \in ledger[n] : Used(h)

NoDoubleAssignment ==
    \A h1, h2 \in Hash :
        (Used(h1) /\ Used(h2) /\ hashes[h1] = hashes[h2]) => h1 = h2

SignaturesValid ==
    \A h \in Hash : Used(h) => VerifySig(hashes[h])

ChainsWellFormed ==
    \A h \in Hash : Used(h) =>
        (hashes[h].prev = NoHash \/ Used(hashes[h].prev))

BalancesSafe ==
    \A h \in Hash : Used(h) =>
        /\ \A n \in Node : BalanceAt(h)[n] >= 0
        /\ SumOver(BalanceAt(h), Node) = TotalFunds

LedgersClosed ==
    \A n \in Node : \A h \in ledger[n] :
        hashes[h].prev = NoHash \/ hashes[h].prev \in ledger[n]

SafetyInvariant ==
    /\ NoDoubleAssignment
    /\ SignaturesValid
    /\ ChainsWellFormed
    /\ BalancesSafe
    /\ LedgersClosed

HashPermanence ==
    [][\A h \in Hash : Used(h) => hashes'[h] = hashes[h]]_vars

ExhaustionStutters ==
    [][~HashesRemain => UNCHANGED vars]_vars

Liveness ==
    \A h \in Hash : (hashes[h] = NoBlock /\ ENABLED ProposeStep) ~> Used(h) \/ ~HashesRemain

=============================================================================