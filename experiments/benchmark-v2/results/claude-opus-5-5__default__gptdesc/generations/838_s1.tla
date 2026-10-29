------------------------------- MODULE MCNano -------------------------------
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
    /\ NoHashVal \notin Hash
    /\ GenesisBalance \in Nat \ {0}
    /\ Cardinality(PrivateKey) = Cardinality(PublicKey)

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

vars == <<hashFunction, lastHash, distributedLedger, received>>

-----------------------------------------------------------------------------
(* Cryptographic primitives and data types of the underlying Nano spec.    *)

KeyPair ==
    CHOOSE f \in [PrivateKey -> PublicKey] :
        \A k1, k2 \in PrivateKey : k1 # k2 => f[k1] # f[k2]

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

Block ==
    GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

Signature == [data : Block, signedWith : PrivateKey]

SignedBlock == [block : Block, signature : Signature]

Ledger == [Hash -> SignedBlock \cup {NoBlockVal}]

SignBlock(b, privKey) ==
    [block |-> b, signature |-> [data |-> b, signedWith |-> privKey]]

ValidateSignature(sb, pubKey) ==
    /\ sb.signature.data = sb.block
    /\ KeyPair[sb.signature.signedWith] = pubKey

-----------------------------------------------------------------------------
(* Model-level hash function: finite state representation of hashing.      *)

UndefinedHashesExist ==
    \E h \in Hash : hashFunction[h] = NoBlockVal

HashOf(b) ==
    IF \E h \in Hash : hashFunction[h] = b
    THEN CHOOSE h \in Hash : hashFunction[h] = b
    ELSE CHOOSE h \in Hash : hashFunction[h] = NoBlockVal

CalculateHashImpl(b, oldLastHash, newLastHash) ==
    LET hash == HashOf(b) IN
    /\ newLastHash = hash
    /\ hashFunction' = [hashFunction EXCEPT ![hash] = b]

-----------------------------------------------------------------------------
(* Ledger helper operators.                                                 *)

InLedger(ledger, h) == ledger[h] # NoBlockVal

BlockAt(ledger, h) == ledger[h].block

RECURSIVE AccountOf(_, _)
AccountOf(ledger, h) ==
    LET b == BlockAt(ledger, h) IN
    IF b.type \in {"genesis", "open"}
    THEN b.account
    ELSE AccountOf(ledger, b.previous)

RECURSIVE BalanceAt(_, _)
BalanceAt(ledger, h) ==
    LET b == BlockAt(ledger, h) IN
    CASE b.type = "genesis" -> b.balance
      [] b.type = "send"    -> b.balance
      [] b.type = "open"    ->
            BalanceAt(ledger, BlockAt(ledger, b.source).previous)
                - BlockAt(ledger, b.source).balance
      [] b.type = "receive" ->
            BalanceAt(ledger, b.previous)
                + (BalanceAt(ledger, BlockAt(ledger, b.source).previous)
                    - BlockAt(ledger, b.source).balance)
      [] OTHER              -> BalanceAt(ledger, b.previous)

SendValue(ledger, h) ==
    BalanceAt(ledger, BlockAt(ledger, h).previous) - BlockAt(ledger, h).balance

IsFrontier(ledger, h) ==
    /\ InLedger(ledger, h)
    /\ ~\E h2 \in Hash :
            /\ InLedger(ledger, h2)
            /\ BlockAt(ledger, h2).type \in {"send", "receive", "change"}
            /\ BlockAt(ledger, h2).previous = h

IsAccountOpen(ledger, acct) ==
    \E h \in Hash :
        /\ InLedger(ledger, h)
        /\ BlockAt(ledger, h).type \in {"genesis", "open"}
        /\ BlockAt(ledger, h).account = acct

SourceUsed(ledger, src) ==
    \E h \in Hash :
        /\ InLedger(ledger, h)
        /\ BlockAt(ledger, h).type \in {"open", "receive"}
        /\ BlockAt(ledger, h).source = src

IsPendingSendTo(ledger, src, acct) ==
    /\ InLedger(ledger, src)
    /\ BlockAt(ledger, src).type = "send"
    /\ BlockAt(ledger, src).link = acct
    /\ ~SourceUsed(ledger, src)

-----------------------------------------------------------------------------
(* Block validation.                                                        *)

ValidSend(ledger, sb) ==
    LET b == sb.block IN
    /\ IsFrontier(ledger, b.previous)
    /\ ValidateSignature(sb, AccountOf(ledger, b.previous))
    /\ b.balance < BalanceAt(ledger, b.previous)

ValidOpen(ledger, sb) ==
    LET b == sb.block IN
    /\ ~IsAccountOpen(ledger, b.account)
    /\ IsPendingSendTo(ledger, b.source, b.account)
    /\ ValidateSignature(sb, b.account)

ValidReceive(ledger, sb) ==
    LET b == sb.block IN
    /\ IsFrontier(ledger, b.previous)
    /\ IsPendingSendTo(ledger, b.source, AccountOf(ledger, b.previous))
    /\ ValidateSignature(sb, AccountOf(ledger, b.previous))

ValidChange(ledger, sb) ==
    LET b == sb.block IN
    /\ IsFrontier(ledger, b.previous)
    /\ ValidateSignature(sb, AccountOf(ledger, b.previous))

ValidBlock(ledger, sb) ==
    CASE sb.block.type = "send"    -> ValidSend(ledger, sb)
      [] sb.block.type = "open"    -> ValidOpen(ledger, sb)
      [] sb.block.type = "receive" -> ValidReceive(ledger, sb)
      [] sb.block.type = "change"  -> ValidChange(ledger, sb)
      [] OTHER                     -> FALSE

-----------------------------------------------------------------------------
(* Nano actions, with hash calculation implemented by CalculateHashImpl.   *)

NanoInit ==
    /\ lastHash = NoHashVal
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privKey) ==
    LET b  == [type |-> "genesis", account |-> KeyPair[privKey],
               balance |-> GenesisBalance]
        sb == SignBlock(b, privKey)
    IN
    /\ lastHash = NoHashVal
    /\ CalculateHashImpl(b, lastHash, lastHash')
    /\ distributedLedger' =
            [n \in Node |-> [distributedLedger[n] EXCEPT ![lastHash'] = sb]]
    /\ UNCHANGED received

CreateBlock(node, privKey, b) ==
    LET ledger == distributedLedger[node]
        sb     == SignBlock(b, privKey)
    IN
    /\ ValidBlock(ledger, sb)
    /\ CalculateHashImpl(b, lastHash, lastHash')
    /\ ~InLedger(ledger, lastHash')
    /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = sb]
    /\ received' = [n \in Node |->
                        IF n = node THEN received[n] ELSE received[n] \cup {sb}]

CreateSend(node, privKey) ==
    \E prev \in Hash, recipient \in PublicKey, bal \in AccountBalance :
        CreateBlock(node, privKey,
            [type |-> "send", previous |-> prev, balance |-> bal, link |-> recipient])

CreateOpen(node, privKey) ==
    \E src \in Hash, rep \in PublicKey :
        CreateBlock(node, privKey,
            [type |-> "open", account |-> KeyPair[privKey], source |-> src, rep |-> rep])

CreateReceive(node, privKey) ==
    \E prev \in Hash, src \in Hash :
        CreateBlock(node, privKey,
            [type |-> "receive", previous |-> prev, source |-> src])

CreateChangeRep(node, privKey) ==
    \E prev \in Hash, rep \in PublicKey :
        CreateBlock(node, privKey,
            [type |-> "change", previous |-> prev, rep |-> rep])

ProcessBlock(node) ==
    \E sb \in received[node] :
        /\ ValidBlock(distributedLedger[node], sb)
        /\ CalculateHashImpl(sb.block, lastHash, lastHash')
        /\ ~InLedger(distributedLedger[node], lastHash')
        /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = sb]
        /\ received' = [received EXCEPT ![node] = @ \ {sb}]

NanoNext ==
    \/ \E privKey \in PrivateKey : CreateGenesisBlock(privKey)
    \/ \E node \in Node, privKey \in PrivateKey :
        \/ CreateSend(node, privKey)
        \/ CreateOpen(node, privKey)
        \/ CreateReceive(node, privKey)
        \/ CreateChangeRep(node, privKey)
    \/ \E node \in Node : ProcessBlock(node)

-----------------------------------------------------------------------------
(* Nano invariants.                                                         *)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

RECURSIVE SumOver(_)
SumOver(f) ==
    IF DOMAIN f = {}
    THEN 0
    ELSE LET x == CHOOSE x \in DOMAIN f : TRUE
         IN  f[x] + SumOver([y \in DOMAIN f \ {x} |-> f[y]])

Frontiers(ledger) == {h \in Hash : IsFrontier(ledger, h)}

PendingSends(ledger) ==
    {h \in Hash : /\ InLedger(ledger, h)
                  /\ BlockAt(ledger, h).type = "send"
                  /\ ~SourceUsed(ledger, h)}

TotalValue(ledger) ==
    SumOver([h \in Frontiers(ledger) |-> BalanceAt(ledger, h)])
        + SumOver([h \in PendingSends(ledger) |-> SendValue(ledger, h)])

SignaturesValid ==
    \A n \in Node, h \in Hash :
        InLedger(distributedLedger[n], h) =>
            ValidateSignature(distributedLedger[n][h],
                              AccountOf(distributedLedger[n], h))

NoDoubleReceive ==
    \A n \in Node, h1, h2 \in Hash :
        LET l == distributedLedger[n] IN
        (/\ h1 # h2
         /\ InLedger(l, h1) /\ InLedger(l, h2)
         /\ BlockAt(l, h1).type \in {"open", "receive"}
         /\ BlockAt(l, h2).type \in {"open", "receive"})
            => BlockAt(l, h1).source # BlockAt(l, h2).source

NoForks ==
    \A n \in Node, h1, h2 \in Hash :
        LET l == distributedLedger[n] IN
        (/\ h1 # h2
         /\ InLedger(l, h1) /\ InLedger(l, h2)
         /\ BlockAt(l, h1).type \in {"send", "receive", "change"}
         /\ BlockAt(l, h2).type \in {"send", "receive", "change"})
            => BlockAt(l, h1).previous # BlockAt(l, h2).previous

ValueConservation ==
    lastHash # NoHashVal =>
        \A n \in Node : TotalValue(distributedLedger[n]) = GenesisBalance

SafetyInvariant ==
    /\ SignaturesValid
    /\ NoDoubleReceive
    /\ NoForks
    /\ ValueConservation

-----------------------------------------------------------------------------
(* Model-checking adaptations.                                              *)

MCTypeInvariant ==
    /\ hashFunction \in [Hash -> Block \cup {NoBlockVal}]
    /\ TypeInvariant

MCSafetyInvariant == SafetyInvariant

Init ==
    /\ hashFunction = [h \in Hash |-> NoBlockVal]
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
    /\ [][Next]_vars

THEOREM Spec => []MCTypeInvariant /\ []MCSafetyInvariant

View == <<distributedLedger, received>>

=============================================================================