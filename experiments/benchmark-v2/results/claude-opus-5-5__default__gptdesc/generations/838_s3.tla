------------------------------- MODULE MCNano -------------------------------
(***************************************************************************)
(* Model-checking adaptation of the Nano blockchain specification.        *)
(* A model-level hash function (hashFunction) and a helper implementation  *)
(* of hash calculation (CalculateHashImpl) let hash assignment be          *)
(* represented with finite state. A stuttering action stops progress       *)
(* gracefully once all available hashes are exhausted. The View ignores    *)
(* hashFunction and lastHash when TLC hashes states.                       *)
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
    /\ Cardinality(PrivateKey) = Cardinality(PublicKey)
    /\ Cardinality(PrivateKey) <= Cardinality(Node)
    /\ GenesisBalance \in Nat
    /\ NoHashVal \notin Hash

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

Vars == <<hashFunction, lastHash, distributedLedger, received>>

View == <<distributedLedger, received>>

-----------------------------------------------------------------------------
(* Key and node ownership mappings                                         *)
-----------------------------------------------------------------------------

KeyPair ==
    CHOOSE mapping \in [PrivateKey -> PublicKey] :
        \A publicKey \in PublicKey :
            \E privateKey \in PrivateKey : mapping[privateKey] = publicKey

Ownership ==
    CHOOSE mapping \in [Node -> PrivateKey] :
        \A privateKey \in PrivateKey :
            \E node \in Node : mapping[node] = privateKey

-----------------------------------------------------------------------------
(* Nano data types                                                         *)
-----------------------------------------------------------------------------

NoHash == NoHashVal

NoBlock == NoBlockVal

AccountBalance == 0 .. GenesisBalance

Signature == [data : Hash, signedWith : PrivateKey]

GenesisBlock ==
    [type : {"genesis"}, account : PublicKey, balance : {GenesisBalance}]

SendBlock ==
    [type : {"send"}, previous : Hash, balance : AccountBalance,
     destination : PublicKey]

OpenBlock ==
    [type : {"open"}, account : PublicKey, source : Hash, rep : PublicKey]

ReceiveBlock ==
    [type : {"receive"}, previous : Hash, source : Hash]

ChangeRepBlock ==
    [type : {"change"}, previous : Hash, rep : PublicKey]

Block ==
    GenesisBlock \cup SendBlock \cup OpenBlock \cup ReceiveBlock \cup ChangeRepBlock

ASSUME NoBlockVal \notin Block

SignedBlock == [block : Block, signature : Signature]

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

SignHash(hash, privateKey) == [data |-> hash, signedWith |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    \E privateKey \in PrivateKey :
        /\ KeyPair[privateKey] = expectedPublicKey
        /\ signature.signedWith = privateKey
        /\ signature.data = expectedHash

-----------------------------------------------------------------------------
(* Model-level hash function implementation                                *)
-----------------------------------------------------------------------------

UndefinedHashesExist ==
    \E hash \in Hash : hashFunction[hash] = NoBlock

HashOf(block) ==
    IF \E hash \in Hash : hashFunction[hash] = block
    THEN CHOOSE hash \in Hash : hashFunction[hash] = block
    ELSE CHOOSE hash \in Hash : hashFunction[hash] = NoBlock

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    LET hash == HashOf(block) IN
    /\ newLastHash = hash
    /\ hashFunction' = [hashFunction EXCEPT ![hash] = block]

-----------------------------------------------------------------------------
(* Ledger queries                                                          *)
-----------------------------------------------------------------------------

HasPrevious(b) == b.type \in {"send", "receive", "change"}

HasSource(b) == b.type \in {"open", "receive"}

RECURSIVE AccountOf(_, _)
AccountOf(L, hash) ==
    LET b == L[hash].block IN
    IF b.type \in {"genesis", "open"}
    THEN b.account
    ELSE AccountOf(L, b.previous)

BlockSigner(L, b) ==
    IF b.type \in {"genesis", "open"}
    THEN b.account
    ELSE AccountOf(L, b.previous)

RECURSIVE BalanceAt(_, _), ValueOfSendBlock(_, _)
BalanceAt(L, hash) ==
    LET b == L[hash].block IN
    CASE b.type = "genesis" -> b.balance
      [] b.type = "open"    -> ValueOfSendBlock(L, b.source)
      [] b.type = "send"    -> b.balance
      [] b.type = "receive" -> BalanceAt(L, b.previous) + ValueOfSendBlock(L, b.source)
      [] b.type = "change"  -> BalanceAt(L, b.previous)

ValueOfSendBlock(L, hash) ==
    BalanceAt(L, L[hash].block.previous) - L[hash].block.balance

IsHead(L, hash) ==
    /\ L[hash] /= NoBlock
    /\ ~\E h2 \in Hash :
            /\ L[h2] /= NoBlock
            /\ HasPrevious(L[h2].block)
            /\ L[h2].block.previous = hash

IsAccountOpen(L, publicKey) ==
    \E hash \in Hash :
        /\ L[hash] /= NoBlock
        /\ L[hash].block.type \in {"genesis", "open"}
        /\ L[hash].block.account = publicKey

IsSendReceived(L, sourceHash) ==
    \E hash \in Hash :
        /\ L[hash] /= NoBlock
        /\ HasSource(L[hash].block)
        /\ L[hash].block.source = sourceHash

ValidSource(L, sourceHash, account) ==
    /\ L[sourceHash] /= NoBlock
    /\ L[sourceHash].block.type = "send"
    /\ L[sourceHash].block.destination = account
    /\ ~IsSendReceived(L, sourceHash)

ValidBlock(L, b) ==
    CASE b.type = "send" ->
            (IsHead(L, b.previous) /\ b.balance < BalanceAt(L, b.previous))
      [] b.type = "open" ->
            (~IsAccountOpen(L, b.account) /\ ValidSource(L, b.source, b.account))
      [] b.type = "receive" ->
            (IsHead(L, b.previous)
                /\ ValidSource(L, b.source, AccountOf(L, b.previous)))
      [] b.type = "change" ->
            IsHead(L, b.previous)
      [] OTHER -> FALSE

GenesisBlockExists ==
    \E n \in Node, hash \in Hash :
        /\ distributedLedger[n][hash] /= NoBlock
        /\ distributedLedger[n][hash].block.type = "genesis"

-----------------------------------------------------------------------------
(* Invariants                                                              *)
-----------------------------------------------------------------------------

TypeInvariant ==
    /\ hashFunction \in [Hash -> Block \cup {NoBlock}]
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicallySecure ==
    \A n \in Node, hash \in Hash :
        LET L == distributedLedger[n] IN
        L[hash] /= NoBlock =>
            ValidateSignature(L[hash].signature, BlockSigner(L, L[hash].block), hash)

AllBalancesValid ==
    \A n \in Node, hash \in Hash :
        LET L == distributedLedger[n] IN
        L[hash] /= NoBlock => BalanceAt(L, hash) \in AccountBalance

NoForks ==
    \A n \in Node, h1, h2 \in Hash :
        LET L == distributedLedger[n] IN
        ( /\ h1 /= h2
          /\ L[h1] /= NoBlock
          /\ L[h2] /= NoBlock
          /\ HasPrevious(L[h1].block)
          /\ HasPrevious(L[h2].block) )
        => L[h1].block.previous /= L[h2].block.previous

UniqueGenesis ==
    \A n \in Node, h1, h2 \in Hash :
        LET L == distributedLedger[n] IN
        ( /\ L[h1] /= NoBlock
          /\ L[h2] /= NoBlock
          /\ L[h1].block.type = "genesis"
          /\ L[h2].block.type = "genesis" )
        => h1 = h2

NanoSafetyInvariant ==
    /\ CryptographicallySecure
    /\ AllBalancesValid
    /\ NoForks
    /\ UniqueGenesis

SafetyInvariant ==
    /\ NanoSafetyInvariant

-----------------------------------------------------------------------------
(* Nano actions                                                            *)
-----------------------------------------------------------------------------

NanoInit ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(privateKey) ==
    LET publicKey == KeyPair[privateKey]
        genesisBlock ==
            [type |-> "genesis", account |-> publicKey, balance |-> GenesisBalance]
    IN
    /\ ~GenesisBlockExists
    /\ CalculateHashImpl(genesisBlock, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |->
            [distributedLedger[n] EXCEPT
                ![lastHash'] = [block |-> genesisBlock,
                                signature |-> SignHash(lastHash', privateKey)]]]
    /\ UNCHANGED received

AddAndBroadcast(node, block, privateKey) ==
    /\ CalculateHashImpl(block, lastHash, lastHash')
    /\ distributedLedger[node][lastHash'] = NoBlock
    /\ LET sb == [block |-> block, signature |-> SignHash(lastHash', privateKey)] IN
       /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = sb]
       /\ received' = [m \in Node |->
                          IF m = node THEN received[m] ELSE received[m] \cup {sb}]

CreateSendBlock(node) ==
    LET privateKey == Ownership[node]
        publicKey == KeyPair[privateKey]
        L == distributedLedger[node]
    IN
    \E prev \in Hash, recipient \in PublicKey, newBalance \in AccountBalance :
        LET block == [type |-> "send", previous |-> prev,
                      balance |-> newBalance, destination |-> recipient]
        IN
        /\ IsHead(L, prev)
        /\ AccountOf(L, prev) = publicKey
        /\ newBalance < BalanceAt(L, prev)
        /\ AddAndBroadcast(node, block, privateKey)

CreateOpenBlock(node) ==
    LET privateKey == Ownership[node]
        publicKey == KeyPair[privateKey]
        L == distributedLedger[node]
    IN
    \E source \in Hash, rep \in PublicKey :
        LET block == [type |-> "open", account |-> publicKey,
                      source |-> source, rep |-> rep]
        IN
        /\ ~IsAccountOpen(L, publicKey)
        /\ ValidSource(L, source, publicKey)
        /\ AddAndBroadcast(node, block, privateKey)

CreateReceiveBlock(node) ==
    LET privateKey == Ownership[node]
        publicKey == KeyPair[privateKey]
        L == distributedLedger[node]
    IN
    \E prev \in Hash, source \in Hash :
        LET block == [type |-> "receive", previous |-> prev, source |-> source] IN
        /\ IsHead(L, prev)
        /\ AccountOf(L, prev) = publicKey
        /\ ValidSource(L, source, publicKey)
        /\ AddAndBroadcast(node, block, privateKey)

CreateChangeRepBlock(node) ==
    LET privateKey == Ownership[node]
        publicKey == KeyPair[privateKey]
        L == distributedLedger[node]
    IN
    \E prev \in Hash, rep \in PublicKey :
        LET block == [type |-> "change", previous |-> prev, rep |-> rep] IN
        /\ IsHead(L, prev)
        /\ AccountOf(L, prev) = publicKey
        /\ AddAndBroadcast(node, block, privateKey)

ProcessBlock(node) ==
    LET L == distributedLedger[node] IN
    \E sb \in received[node] :
        /\ ValidBlock(L, sb.block)
        /\ CalculateHashImpl(sb.block, lastHash, lastHash')
        /\ L[lastHash'] = NoBlock
        /\ ValidateSignature(sb.signature, BlockSigner(L, sb.block), lastHash')
        /\ distributedLedger' = [distributedLedger EXCEPT ![node][lastHash'] = sb]
        /\ received' = [received EXCEPT ![node] = @ \ {sb}]

NanoNext ==
    \/ \E privateKey \in PrivateKey : CreateGenesisBlock(privateKey)
    \/ \E node \in Node :
        \/ CreateSendBlock(node)
        \/ CreateOpenBlock(node)
        \/ CreateReceiveBlock(node)
        \/ CreateChangeRepBlock(node)
        \/ ProcessBlock(node)

-----------------------------------------------------------------------------
(* Model-checking specification                                            *)
-----------------------------------------------------------------------------

Init ==
    /\ hashFunction = [hash \in Hash |-> NoBlock]
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