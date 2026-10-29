------------------------------ MODULE Nano ------------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
    CalculateHash(_, _, _),
    Hash,
    NoHashVal,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance,
    NoBlockVal

NoHash == NoHashVal
NoBlock == NoBlockVal

ASSUME
    /\ Cardinality(PrivateKey) = Cardinality(PublicKey)
    /\ GenesisBalance \in Nat

KeyPair ==
    CHOOSE mapping \in [PrivateKey -> PublicKey] :
        \A k1, k2 \in PrivateKey : k1 # k2 => mapping[k1] # mapping[k2]

Signature == [data : Hash, signedWith : PrivateKey]

SignHash(hash, privateKey) == [data |-> hash, signedWith |-> privateKey]

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type : {"genesis"}, account : PublicKey, balance : {GenesisBalance}]

SendBlock ==
    [previous : Hash, balance : AccountBalance, link : PublicKey, type : {"send"}]

OpenBlock ==
    [account : PublicKey, source : Hash, rep : PublicKey, type : {"open"}]

ReceiveBlock ==
    [previous : Hash, source : Hash, type : {"receive"}]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock

SignedBlock == [block : Block, signature : Signature]

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

vars == <<hashFunction, lastHash, distributedLedger, received>>

View == <<distributedLedger, received>>

-----------------------------------------------------------------------------
(* Hash function implementation for model checking *)

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
(* Ledger helper operators *)

Validated(ledger) == {h \in Hash : ledger[h] # NoBlock}

HasPrevious(ledger, h) == ledger[h].block.type \in {"send", "receive"}

HasSource(ledger, h) == ledger[h].block.type \in {"open", "receive"}

RECURSIVE BlockAccount(_, _)
BlockAccount(ledger, hash) ==
    LET b == ledger[hash].block IN
    IF b.type \in {"genesis", "open"}
    THEN b.account
    ELSE BlockAccount(ledger, b.previous)

RECURSIVE BalanceAt(_, _), ValueOfSend(_, _)
BalanceAt(ledger, hash) ==
    LET b == ledger[hash].block IN
    CASE b.type = "genesis" -> b.balance
      [] b.type = "send"    -> b.balance
      [] b.type = "open"    -> ValueOfSend(ledger, b.source)
      [] OTHER              -> BalanceAt(ledger, b.previous)
                                 + ValueOfSend(ledger, b.source)

ValueOfSend(ledger, hash) ==
    BalanceAt(ledger, ledger[hash].block.previous) - ledger[hash].block.balance

IsFrontier(ledger, hash) ==
    ~\E h \in Validated(ledger) :
        /\ HasPrevious(ledger, h)
        /\ ledger[h].block.previous = hash

AccountOpen(ledger, account) ==
    \E h \in Validated(ledger) :
        /\ ledger[h].block.type \in {"genesis", "open"}
        /\ ledger[h].block.account = account

Frontier(ledger, account) ==
    CHOOSE h \in Validated(ledger) :
        /\ BlockAccount(ledger, h) = account
        /\ IsFrontier(ledger, h)

AccountBalanceOf(ledger, account) ==
    IF AccountOpen(ledger, account)
    THEN BalanceAt(ledger, Frontier(ledger, account))
    ELSE 0

SendReceived(ledger, sendHash) ==
    \E h \in Validated(ledger) :
        /\ HasSource(ledger, h)
        /\ ledger[h].block.source = sendHash

IsUnreceivedSendTo(ledger, s, account) ==
    /\ ledger[s] # NoBlock
    /\ ledger[s].block.type = "send"
    /\ ledger[s].block.link = account
    /\ ~SendReceived(ledger, s)

PendingSends(ledger) ==
    {h \in Validated(ledger) :
        /\ ledger[h].block.type = "send"
        /\ ~SendReceived(ledger, h)}

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TotalFunds(ledger) ==
    LET pending == PendingSends(ledger) IN
    SumOver([a \in PublicKey |-> AccountBalanceOf(ledger, a)], PublicKey)
      + SumOver([h \in pending |-> ValueOfSend(ledger, h)], pending)

Parents(ledger, S) ==
    {ledger[x].block.previous :
        x \in {y \in S : ledger[y] # NoBlock /\ HasPrevious(ledger, y)}}

RECURSIVE Iterate(_, _, _)
Iterate(ledger, S, k) ==
    IF k = 0 THEN S
    ELSE Iterate(ledger, S \cup Parents(ledger, S), k - 1)

StrictAncestors(ledger, h) ==
    Iterate(ledger, Parents(ledger, {h}), Cardinality(Hash))

ValidBlock(ledger, sb) ==
    LET b == sb.block
        signer == KeyPair[sb.signature.signedWith]
    IN
    CASE b.type = "send" ->
            /\ ledger[b.previous] # NoBlock
            /\ IsFrontier(ledger, b.previous)
            /\ signer = BlockAccount(ledger, b.previous)
            /\ b.balance < BalanceAt(ledger, b.previous)
      [] b.type = "open" ->
            /\ ~AccountOpen(ledger, b.account)
            /\ IsUnreceivedSendTo(ledger, b.source, b.account)
            /\ signer = b.account
      [] b.type = "receive" ->
            /\ ledger[b.previous] # NoBlock
            /\ IsFrontier(ledger, b.previous)
            /\ IsUnreceivedSendTo(ledger, b.source,
                                  BlockAccount(ledger, b.previous))
            /\ signer = BlockAccount(ledger, b.previous)
      [] OTHER -> FALSE

-----------------------------------------------------------------------------
(* Invariants *)

TypeInvariant ==
    /\ hashFunction \in [Hash -> Block \cup {NoBlockVal}]
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

ChainIntegrity(ledger) ==
    /\ \A h \in Validated(ledger) :
        /\ HasPrevious(ledger, h) =>
            /\ ledger[ledger[h].block.previous] # NoBlock
            /\ ledger[h].block.previous # h
        /\ HasSource(ledger, h) =>
            /\ ledger[ledger[h].block.source] # NoBlock
            /\ ledger[ledger[h].block.source].block.type = "send"
    /\ \A h \in Validated(ledger) : h \notin StrictAncestors(ledger, h)

SignaturesValid(ledger) ==
    \A h \in Validated(ledger) :
        /\ ledger[h].signature.data = h
        /\ KeyPair[ledger[h].signature.signedWith] = BlockAccount(ledger, h)

NoDoubleSpend(ledger) ==
    /\ \A h1, h2 \in Validated(ledger) :
        /\ (h1 # h2 /\ HasPrevious(ledger, h1) /\ HasPrevious(ledger, h2))
            => ledger[h1].block.previous # ledger[h2].block.previous
        /\ (h1 # h2 /\ HasSource(ledger, h1) /\ HasSource(ledger, h2))
            => ledger[h1].block.source # ledger[h2].block.source
        /\ (h1 # h2 /\ ledger[h1].block.type \in {"genesis", "open"}
                    /\ ledger[h2].block.type \in {"genesis", "open"})
            => ledger[h1].block.account # ledger[h2].block.account
    /\ \A h \in Validated(ledger) :
        ledger[h].block.type = "send" =>
            ledger[h].block.balance < BalanceAt(ledger, ledger[h].block.previous)
    /\ \A h \in Validated(ledger) :
        /\ ledger[h].block.type = "open" =>
            ledger[ledger[h].block.source].block.link = ledger[h].block.account
        /\ ledger[h].block.type = "receive" =>
            ledger[ledger[h].block.source].block.link
                = BlockAccount(ledger, ledger[h].block.previous)

ConservationOfFunds(ledger) ==
    Validated(ledger) # {} => TotalFunds(ledger) = GenesisBalance

SafetyInvariant ==
    \A n \in Node :
        LET ledger == distributedLedger[n] IN
        /\ ChainIntegrity(ledger)
        /\ SignaturesValid(ledger)
        /\ NoDoubleSpend(ledger)
        /\ ConservationOfFunds(ledger)

-----------------------------------------------------------------------------
(* Actions *)

Init ==
    /\ hashFunction = [h \in Hash |-> NoBlockVal]
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privKey) ==
    LET pub == KeyPair[privKey]
        genesis == [type |-> "genesis", account |-> pub,
                    balance |-> GenesisBalance]
    IN
    /\ lastHash = NoHash
    /\ CalculateHash(genesis, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |->
            [distributedLedger[n] EXCEPT
                ![lastHash'] = [block |-> genesis,
                                signature |-> SignHash(lastHash', privKey)]]]
    /\ UNCHANGED received

CreateSendBlock(node) ==
    LET ledger == distributedLedger[node] IN
    \E privKey \in PrivateKey, recipient \in PublicKey :
        LET pub == KeyPair[privKey] IN
        /\ AccountOpen(ledger, pub)
        /\ LET prev == Frontier(ledger, pub)
               bal == BalanceAt(ledger, prev)
           IN
           \E newBal \in 0 .. (bal - 1) :
               LET blk == [previous |-> prev, balance |-> newBal,
                           link |-> recipient, type |-> "send"]
               IN
               /\ CalculateHash(blk, lastHash, lastHash')
               /\ received' = [received EXCEPT ![node] =
                    @ \cup {[block |-> blk,
                             signature |-> SignHash(lastHash', privKey)]}]
               /\ UNCHANGED distributedLedger

CreateOpenBlock(node) ==
    LET ledger == distributedLedger[node] IN
    \E privKey \in PrivateKey, s \in Validated(ledger) :
        LET pub == KeyPair[privKey]
            blk == [account |-> pub, source |-> s, rep |-> pub, type |-> "open"]
        IN
        /\ ~AccountOpen(ledger, pub)
        /\ IsUnreceivedSendTo(ledger, s, pub)
        /\ CalculateHash(blk, lastHash, lastHash')
        /\ received' = [received EXCEPT ![node] =
             @ \cup {[block |-> blk,
                      signature |-> SignHash(lastHash', privKey)]}]
        /\ UNCHANGED distributedLedger

CreateReceiveBlock(node) ==
    LET ledger == distributedLedger[node] IN
    \E privKey \in PrivateKey, s \in Validated(ledger) :
        LET pub == KeyPair[privKey] IN
        /\ AccountOpen(ledger, pub)
        /\ IsUnreceivedSendTo(ledger, s, pub)
        /\ LET blk == [previous |-> Frontier(ledger, pub), source |-> s,
                       type |-> "receive"]
           IN
           /\ CalculateHash(blk, lastHash, lastHash')
           /\ received' = [received EXCEPT ![node] =
                @ \cup {[block |-> blk,
                         signature |-> SignHash(lastHash', privKey)]}]
           /\ UNCHANGED distributedLedger

ProcessBlock(node) ==
    LET ledger == distributedLedger[node] IN
    \E sb \in received[node] :
        LET h == sb.signature.data IN
        /\ ledger[h] = NoBlock
        /\ ValidBlock(ledger, sb)
        /\ distributedLedger' = [distributedLedger EXCEPT ![node][h] = sb]
        /\ UNCHANGED <<hashFunction, lastHash, received>>

BroadcastBlock(node) ==
    LET ledger == distributedLedger[node] IN
    \E h \in Validated(ledger) :
        /\ \E n \in Node : ledger[h] \notin received[n]
        /\ received' = [n \in Node |-> received[n] \cup {ledger[h]}]
        /\ UNCHANGED <<hashFunction, lastHash, distributedLedger>>

HashingAction ==
    /\ UndefinedHashesExist
    /\ \/ \E privKey \in PrivateKey : CreateGenesisBlock(privKey)
       \/ \E node \in Node :
            \/ CreateSendBlock(node)
            \/ CreateOpenBlock(node)
            \/ CreateReceiveBlock(node)

StutterWhenHashesDepleted ==
    /\ ~UndefinedHashesExist
    /\ UNCHANGED vars

Next ==
    \/ HashingAction
    \/ \E node \in Node : ProcessBlock(node)
    \/ \E node \in Node : BroadcastBlock(node)
    \/ StutterWhenHashesDepleted

Spec ==
    /\ Init
    /\ [][Next]_vars

=============================================================================