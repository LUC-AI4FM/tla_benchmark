------------------------------- MODULE MCNano ------------------------------
EXTENDS Naturals, FiniteSets

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

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

Vars == <<hashFunction, lastHash, distributedLedger, received>>

View == <<distributedLedger, received>>

KeyPair ==
    CHOOSE mapping \in [PrivateKey -> PublicKey] :
        \A publicKey \in PublicKey :
            \E privateKey \in PrivateKey : mapping[privateKey] = publicKey

Ownership ==
    CHOOSE mapping \in [Node -> PrivateKey] :
        \A privateKey \in PrivateKey :
            \E node \in Node : mapping[node] = privateKey

NoBlockLocal == NoBlockVal

UndefinedHashesExist ==
    \E hash \in Hash : hashFunction[hash] = NoBlockLocal

HashOf(block) ==
    IF \E hash \in Hash : hashFunction[hash] = block
    THEN CHOOSE hash \in Hash : hashFunction[hash] = block
    ELSE CHOOSE hash \in Hash : hashFunction[hash] = NoBlockLocal

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    LET hash == HashOf(block) IN
    /\ newLastHash = hash
    /\ hashFunction' = [hashFunction EXCEPT ![hash] = block]

N == INSTANCE Nano WITH
    CalculateHash <- CalculateHashImpl,
    Hash <- Hash,
    NoHashVal <- NoHashVal,
    PrivateKey <- PrivateKey,
    PublicKey <- PublicKey,
    KeyPair <- KeyPair,
    Node <- Node,
    GenesisBalance <- GenesisBalance,
    Ownership <- Ownership,
    NoBlockVal <- NoBlockVal,
    lastHash <- lastHash,
    distributedLedger <- distributedLedger,
    received <- received

TypeInvariant ==
    /\ hashFunction \in [Hash -> N!Block \cup {N!NoBlock}]
    /\ N!TypeInvariant

SafetyInvariant ==
    N!SafetyInvariant

Init ==
    /\ hashFunction = [hash \in Hash |-> N!NoBlock]
    /\ N!Init

StutterWhenHashesDepleted ==
    UNCHANGED Vars

Next ==
    IF UndefinedHashesExist
    THEN N!Next
    ELSE StutterWhenHashesDepleted

Spec ==
    /\ Init
    /\ [][Next]_Vars

=============================================================================