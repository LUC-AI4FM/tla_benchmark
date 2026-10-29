------------------------------- MODULE MCNano -------------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
    CalculateHash(_,_,_),
    Hash,
    NoHash,
    NoHashVal,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance,
    NoBlock,
    NoBlockVal

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

Vars == <<hashFunction, lastHash, distributedLedger, received>>

View == <<distributedLedger, received>>

ASSUME NoHash \notin Hash
ASSUME GenesisBalance \in Nat
ASSUME Cardinality(PrivateKey) = Cardinality(PublicKey)
ASSUME Cardinality(Node) <= Cardinality(PrivateKey)

-----------------------------------------------------------------------------
(* Underlying Nano definitions *)

AccountBalance == 0 .. GenesisBalance

KeyPair ==
    CHOOSE mapping \in [PrivateKey -> PublicKey] :
        \A k1, k2 \in PrivateKey : mapping[k1] = mapping[k2] => k1 = k2

Ownership ==
    CHOOSE mapping \in [Node -> PrivateKey] :
        \A n1, n2 \in Node : mapping[n1] = mapping[n2] => n1 = n2

Signature == [data : Hash, signedWith : PrivateKey]

Sign(data, privateKey) == [data |-> data, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedData) ==
    /\ KeyPair[signature.signedWith] = expectedPublicKey
    /\ signature.data = expectedData

GenesisBlock ==
    [type : {"genesis"}, account : PublicKey, balance : {GenesisBalance}]

SendBlock ==
    [type : {"send"}, previous : Hash, balance : AccountBalance, link : PublicKey]

OpenBlock ==
    [type : {"open"}, account : PublicKey, representative : PublicKey, link : Hash]

ReceiveBlock ==
    [type : {"receive"}, previous : Hash, link : Hash]

ChangeRepBlock ==
    [type : {"change"}, previous : Hash, representative : PublicKey]

Block == GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

CandidateBlock == SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

SignedBlock == [block : Block, signature : Signature]

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

Exists(ledger, h) == ledger[h] # NoBlock

HasPrevious(b) == b.type \in {"send", "receive", "change"}

IsTop(ledger, h) ==
    ~\E h2 \in Hash :
        /\ Exists(ledger, h2)
        /\ HasPrevious(ledger[h2].block)
        /\ ledger[h2].block.previous = h

IsAccountOpen(ledger, publicKey) ==
    \E h \in Hash :
        /\ Exists(ledger, h)
        /\ ledger[h].block.type \in {"genesis", "open"}
        /\ ledger[h].block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    \E h \in Hash :
        /\ Exists(ledger, h)
        /\ ledger[h].block.type \in {"open", "receive"}
        /\ ledger[h].block.link = sourceHash

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(ledger, h) ==
    LET b == ledger[h].block IN
    IF b.type \in {"genesis", "open"}
    THEN b.account
    ELSE PublicKeyOf(ledger, b.previous)

RECURSIVE BalanceAt(_, _)
BalanceAt(ledger, h) ==
    LET b == ledger[h].block IN
    CASE b.type = "genesis" -> b.balance
      [] b.type = "send"    -> b.balance
      [] b.type = "open"    ->
            BalanceAt(ledger, ledger[b.link].block.previous)
                - ledger[b.link].block.balance
      [] b.type = "receive" ->
            BalanceAt(ledger, b.previous)
                + (BalanceAt(ledger, ledger[b.link].block.previous)
                    - ledger[b.link].block.balance)
      [] b.type = "change"  -> BalanceAt(ledger, b.previous)

ValidateBlock(ledger, h, sb) ==
    LET b == sb.block IN
    /\ ~Exists(ledger, h)
    /\ CASE b.type = "genesis" -> FALSE
         [] b.type = "send" ->
              /\ Exists(ledger, b.previous)
              /\ IsTop(ledger, b.previous)
              /\ ValidateSignature(sb.signature, PublicKeyOf(ledger, b.previous), h)
              /\ b.balance < BalanceAt(ledger, b.previous)
         [] b.type = "open" ->
              /\ Exists(ledger, b.link)
              /\ ledger[b.link].block.type = "send"
              /\ ledger[b.link].block.link = b.account
              /\ ~IsAccountOpen(ledger, b.account)
              /\ ~IsSendReceived(ledger, b.link)
              /\ ValidateSignature(sb.signature, b.account, h)
         [] b.type = "receive" ->
              /\ Exists(ledger, b.previous)
              /\ IsTop(ledger, b.previous)
              /\ Exists(ledger, b.link)
              /\ ledger[b.link].block.type = "send"
              /\ ledger[b.link].block.link = PublicKeyOf(ledger, b.previous)
              /\ ~IsSendReceived(ledger, b.link)
              /\ ValidateSignature(sb.signature, PublicKeyOf(ledger, b.previous), h)
         [] b.type = "change" ->
              /\ Exists(ledger, b.previous)
              /\ IsTop(ledger, b.previous)
              /\ ValidateSignature(sb.signature, PublicKeyOf(ledger, b.previous), h)

-----------------------------------------------------------------------------
(* Model-checking helpers *)

UndefinedHashesExist ==
    \E h \in Hash : hashFunction[h] = NoBlock

HashOf(block) ==
    IF \E h \in Hash : hashFunction[h] = block
    THEN CHOOSE h \in Hash : hashFunction[h] = block
    ELSE CHOOSE h \in Hash : hashFunction[h] = NoBlock

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    LET h == HashOf(block) IN
    /\ newLastHash = h
    /\ hashFunction' = [hashFunction EXCEPT ![h] = block]

-----------------------------------------------------------------------------
(* Nano behavior *)

NanoInit ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock ==
    /\ lastHash = NoHash
    /\ \E pk \in PrivateKey :
        LET g == [type |-> "genesis", account |-> KeyPair[pk],
                  balance |-> GenesisBalance] IN
        /\ CalculateHash(g, lastHash, lastHash')
        /\ distributedLedger' =
             [n \in Node |->
                [distributedLedger[n] EXCEPT
                    ![lastHash'] = [block |-> g, signature |-> Sign(lastHash', pk)]]]
        /\ UNCHANGED received

CreateBlock(node) ==
    /\ lastHash # NoHash
    /\ \E b \in CandidateBlock :
        /\ CalculateHash(b, lastHash, lastHash')
        /\ LET sb == [block |-> b, signature |-> Sign(lastHash', Ownership[node])] IN
           /\ ValidateBlock(distributedLedger[node], lastHash', sb)
           /\ distributedLedger' =
                [distributedLedger EXCEPT ![node][lastHash'] = sb]
           /\ received' =
                [n \in Node |->
                    IF n = node THEN received[n] ELSE received[n] \cup {sb}]

ProcessBlock(node) ==
    \E sb \in received[node] :
        /\ CalculateHash(sb.block, lastHash, lastHash')
        /\ ValidateBlock(distributedLedger[node], lastHash', sb)
        /\ distributedLedger' =
             [distributedLedger EXCEPT ![node][lastHash'] = sb]
        /\ received' = [received EXCEPT ![node] = @ \ {sb}]

NanoNext ==
    \/ CreateGenesisBlock
    \/ \E node \in Node : CreateBlock(node)
    \/ \E node \in Node : ProcessBlock(node)

-----------------------------------------------------------------------------
(* Invariants *)

NanoTypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

TypeInvariant ==
    /\ hashFunction \in [Hash -> Block \cup {NoBlock}]
    /\ NanoTypeInvariant

CryptographicallySecure ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A h \in Hash :
            Exists(ledger, h) =>
                ValidateSignature(ledger[h].signature, PublicKeyOf(ledger, h), h)

NoOverspend ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A h \in Hash :
            Exists(ledger, h) => BalanceAt(ledger, h) \in AccountBalance

UniqueGenesis ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A h1, h2 \in Hash :
            (/\ Exists(ledger, h1) /\ ledger[h1].block.type = "genesis"
             /\ Exists(ledger, h2) /\ ledger[h2].block.type = "genesis") => h1 = h2

NoDoubleReceive ==
    \A node \in Node :
        LET ledger == distributedLedger[node] IN
        \A h1, h2 \in Hash :
            (/\ Exists(ledger, h1) /\ ledger[h1].block.type \in {"open", "receive"}
             /\ Exists(ledger, h2) /\ ledger[h2].block.type \in {"open", "receive"}
             /\ ledger[h1].block.link = ledger[h2].block.link) => h1 = h2

NanoSafetyInvariant ==
    /\ CryptographicallySecure
    /\ NoOverspend
    /\ UniqueGenesis
    /\ NoDoubleReceive

SafetyInvariant ==
    /\ NanoSafetyInvariant

-----------------------------------------------------------------------------
(* Model-checking specification *)

Init ==
    /\ hashFunction = [h \in Hash |-> NoBlock]
    /\ NanoInit

StutterWhenHashesDepleted ==
    /\ UNCHANGED hashFunction
    /\ UNCHANGED lastHash
    /\ UNCHANGED distributedLedger
    /\ UNCHANGED received

Next ==
    IF UndefinedHashesExist
    THEN NanoNext
    ELSE StutterWhenHashesDepleted

Spec ==
    /\ Init
    /\ [][Next]_Vars

THEOREM Safety == Spec => [](TypeInvariant /\ SafetyInvariant)
=============================================================================