------------------------------- MODULE MCNano -------------------------------
(***************************************************************************)
(* Model-checking adaptation of the Nano blockchain specification.        *)
(* A model-level hash function (hashFunction) and a helper implementation *)
(* of hash calculation (CalculateHashImpl) let hash assignment use finite *)
(* state. A stuttering action stops progress gracefully once all          *)
(* available hashes are used up. The View ignores hashFunction and        *)
(* lastHash when TLC hashes states.                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash,           \* Finite set of available hash values
    NoHashVal,      \* Sentinel: no hash
    PrivateKey,     \* Set of private keys
    PublicKey,      \* Set of public keys
    KeyPair,        \* Function mapping each private key to its public key
    Node,           \* Set of nodes in the network
    Ownership,      \* Function mapping each node to the private key it owns
    GenesisBalance, \* Total balance created by the genesis block
    NoBlockVal      \* Sentinel: no block

VARIABLES
    hashFunction,       \* Model-level hash function: Hash -> Block or NoBlockVal
    lastHash,           \* Most recently calculated hash
    distributedLedger,  \* Each node's ledger: Node -> (Hash -> SignedBlock)
    received            \* Blocks broadcast to each node

vars == <<hashFunction, lastHash, distributedLedger, received>>

\* View used by TLC for state hashing; ignores hashFunction and lastHash.
View == <<distributedLedger, received>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Data types                                                              *)
(***************************************************************************)
AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type : {"genesis"}, account : PublicKey, balance : {GenesisBalance}]

SendBlock ==
    [type : {"send"}, previous : Hash, balance : AccountBalance, link : PublicKey]

OpenBlock ==
    [type : {"open"}, account : PublicKey, source : Hash, rep : PublicKey]

ReceiveBlock ==
    [type : {"receive"}, previous : Hash, source : Hash]

ChangeRepBlock ==
    [type : {"change"}, previous : Hash, rep : PublicKey]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

Signature == [data : Block, signedWith : PrivateKey]

SignedBlock == [block : Block, signature : Signature]

Sign(block, privateKey) == [data |-> block, signedWith |-> privateKey]

SignBlock(block, privateKey) ==
    [block |-> block, signature |-> Sign(block, privateKey)]

ASSUME
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ Ownership \in [Node -> PrivateKey]
    /\ GenesisBalance \in Nat
    /\ NoHashVal \notin Hash
    /\ NoBlockVal \notin Block

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
(* Ledger helper operators                                                 *)
(***************************************************************************)
Defined(ledger, h) == ledger[h] # NoBlockVal

RECURSIVE AccountOf(_, _)
AccountOf(ledger, h) ==
    LET b == ledger[h].block IN
    IF b.type \in {"genesis", "open"}
    THEN b.account
    ELSE AccountOf(ledger, b.previous)

RECURSIVE BalanceAt(_, _), ValueOfSendBlock(_, _)
BalanceAt(ledger, h) ==
    LET b == ledger[h].block IN
    CASE b.type = "genesis" -> b.balance
      [] b.type = "send"    -> b.balance
      [] b.type = "open"    -> ValueOfSendBlock(ledger, b.source)
      [] b.type = "receive" -> BalanceAt(ledger, b.previous)
                                 + ValueOfSendBlock(ledger, b.source)
      [] b.type = "change"  -> BalanceAt(ledger, b.previous)

ValueOfSendBlock(ledger, h) ==
    BalanceAt(ledger, ledger[h].block.previous) - ledger[h].block.balance

IsFrontier(ledger, h) ==
    \A h2 \in Hash :
        Defined(ledger, h2) =>
            \/ ledger[h2].block.type \in {"genesis", "open"}
            \/ ledger[h2].block.previous # h

AlreadyReceived(ledger, src) ==
    \E h \in Hash :
        /\ Defined(ledger, h)
        /\ ledger[h].block.type \in {"open", "receive"}
        /\ ledger[h].block.source = src

AccountOpen(ledger, acct) ==
    \E h \in Hash :
        /\ Defined(ledger, h)
        /\ ledger[h].block.type \in {"genesis", "open"}
        /\ ledger[h].block.account = acct

IsSendTo(ledger, src, acct) ==
    /\ Defined(ledger, src)
    /\ ledger[src].block.type = "send"
    /\ ledger[src].block.link = acct

Broadcast(signedBlock) ==
    received' = [n \in Node |-> received[n] \cup {signedBlock}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Block creation actions                                                  *)
(***************************************************************************)
CreateGenesisBlock ==
    /\ lastHash = NoHashVal
    /\ \E privateKey \in PrivateKey :
        LET block == [type    |-> "genesis",
                      account |-> KeyPair[privateKey],
                      balance |-> GenesisBalance]
        IN
        /\ CalculateHashImpl(block, lastHash, lastHash')
        /\ Broadcast(SignBlock(block, privateKey))
        /\ UNCHANGED distributedLedger

CreateSendBlock(node) ==
    LET ledger     == distributedLedger[node]
        privateKey == Ownership[node]
        account    == KeyPair[privateKey]
    IN
    \E prev \in Hash :
        /\ Defined(ledger, prev)
        /\ AccountOf(ledger, prev) = account
        /\ IsFrontier(ledger, prev)
        /\ BalanceAt(ledger, prev) > 0
        /\ \E recipient \in PublicKey,
              newBalance \in 0 .. (BalanceAt(ledger, prev) - 1) :
            LET block == [type     |-> "send",
                          previous |-> prev,
                          balance  |-> newBalance,
                          link     |-> recipient]
            IN
            /\ CalculateHashImpl(block, lastHash, lastHash')
            /\ Broadcast(SignBlock(block, privateKey))
            /\ UNCHANGED distributedLedger

CreateOpenBlock(node) ==
    LET ledger     == distributedLedger[node]
        privateKey == Ownership[node]
        account    == KeyPair[privateKey]
    IN
    /\ ~AccountOpen(ledger, account)
    /\ \E src \in Hash, rep \in PublicKey :
        /\ IsSendTo(ledger, src, account)
        /\ ~AlreadyReceived(ledger, src)
        /\ LET block == [type    |-> "open",
                         account |-> account,
                         source  |-> src,
                         rep     |-> rep]
           IN
           /\ CalculateHashImpl(block, lastHash, lastHash')
           /\ Broadcast(SignBlock(block, privateKey))
           /\ UNCHANGED distributedLedger

CreateReceiveBlock(node) ==
    LET ledger     == distributedLedger[node]
        privateKey == Ownership[node]
        account    == KeyPair[privateKey]
    IN
    \E prev \in Hash, src \in Hash :
        /\ Defined(ledger, prev)
        /\ AccountOf(ledger, prev) = account
        /\ IsFrontier(ledger, prev)
        /\ IsSendTo(ledger, src, account)
        /\ ~AlreadyReceived(ledger, src)
        /\ LET block == [type     |-> "receive",
                         previous |-> prev,
                         source   |-> src]
           IN
           /\ CalculateHashImpl(block, lastHash, lastHash')
           /\ Broadcast(SignBlock(block, privateKey))
           /\ UNCHANGED distributedLedger

CreateChangeRepBlock(node) ==
    LET ledger     == distributedLedger[node]
        privateKey == Ownership[node]
        account    == KeyPair[privateKey]
    IN
    \E prev \in Hash, rep \in PublicKey :
        /\ Defined(ledger, prev)
        /\ AccountOf(ledger, prev) = account
        /\ IsFrontier(ledger, prev)
        /\ LET block == [type     |-> "change",
                         previous |-> prev,
                         rep      |-> rep]
           IN
           /\ CalculateHashImpl(block, lastHash, lastHash')
           /\ Broadcast(SignBlock(block, privateKey))
           /\ UNCHANGED distributedLedger

-----------------------------------------------------------------------------
(***************************************************************************)
(* Block validation and processing                                         *)
(***************************************************************************)
ValidateBlock(ledger, sb) ==
    LET b      == sb.block
        signer == KeyPair[sb.signature.signedWith]
    IN
    /\ sb.signature.data = b
    /\ CASE b.type = "genesis" ->
              ( /\ \A h \in Hash : ~Defined(ledger, h)
                /\ signer = b.account )
         [] b.type = "send" ->
              ( /\ Defined(ledger, b.previous)
                /\ IsFrontier(ledger, b.previous)
                /\ b.balance < BalanceAt(ledger, b.previous)
                /\ signer = AccountOf(ledger, b.previous) )
         [] b.type = "open" ->
              ( /\ ~AccountOpen(ledger, b.account)
                /\ IsSendTo(ledger, b.source, b.account)
                /\ ~AlreadyReceived(ledger, b.source)
                /\ signer = b.account )
         [] b.type = "receive" ->
              ( /\ Defined(ledger, b.previous)
                /\ IsFrontier(ledger, b.previous)
                /\ IsSendTo(ledger, b.source, AccountOf(ledger, b.previous))
                /\ ~AlreadyReceived(ledger, b.source)
                /\ signer = AccountOf(ledger, b.previous) )
         [] b.type = "change" ->
              ( /\ Defined(ledger, b.previous)
                /\ IsFrontier(ledger, b.previous)
                /\ signer = AccountOf(ledger, b.previous) )

ProcessBlock(node) ==
    LET ledger == distributedLedger[node] IN
    \E sb \in received[node], h \in Hash :
        /\ hashFunction[h] = sb.block
        /\ ~Defined(ledger, h)
        /\ ValidateBlock(ledger, sb)
        /\ distributedLedger' = [distributedLedger EXCEPT ![node][h] = sb]
        /\ UNCHANGED <<hashFunction, lastHash, received>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Init ==
    /\ hashFunction = [h \in Hash |-> NoBlockVal]
    /\ lastHash = NoHashVal
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

NanoNext ==
    \/ CreateGenesisBlock
    \/ \E node \in Node :
        \/ CreateSendBlock(node)
        \/ CreateOpenBlock(node)
        \/ CreateReceiveBlock(node)
        \/ CreateChangeRepBlock(node)
        \/ ProcessBlock(node)

\* Stop progress gracefully once all available hashes are used.
StutterWhenHashesDepleted ==
    /\ ~UndefinedHashesExist
    /\ UNCHANGED vars

Next ==
    \/ /\ UndefinedHashesExist
       /\ NanoNext
    \/ StutterWhenHashesDepleted

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeInvariant ==
    /\ hashFunction \in [Hash -> Block \cup {NoBlockVal}]
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ DOMAIN distributedLedger = Node
    /\ \A n \in Node :
        /\ DOMAIN distributedLedger[n] = Hash
        /\ \A h \in Hash :
            distributedLedger[n][h] \in SignedBlock \cup {NoBlockVal}
    /\ DOMAIN received = Node
    /\ \A n \in Node : received[n] \subseteq SignedBlock

SafetyInvariant ==
    /\ \A n \in Node :
        LET ledger == distributedLedger[n] IN
        /\ \A h \in Hash :
            Defined(ledger, h) =>
                /\ ledger[h].signature.data = ledger[h].block
                /\ hashFunction[h] = ledger[h].block
                /\ KeyPair[ledger[h].signature.signedWith] = AccountOf(ledger, h)
                /\ BalanceAt(ledger, h) \in AccountBalance
        /\ \A h1, h2 \in Hash :
            ( /\ h1 # h2
              /\ Defined(ledger, h1)
              /\ Defined(ledger, h2)
              /\ ledger[h1].block.type \in {"open", "receive"}
              /\ ledger[h2].block.type \in {"open", "receive"} )
            => ledger[h1].block.source # ledger[h2].block.source
    /\ \A n1, n2 \in Node, h \in Hash :
        ( Defined(distributedLedger[n1], h) /\ Defined(distributedLedger[n2], h) )
        => distributedLedger[n1][h] = distributedLedger[n2][h]

SafetyProperty == [](TypeInvariant /\ SafetyInvariant)

THEOREM Spec => SafetyProperty

=============================================================================