------------------------------- MODULE MCNano -------------------------------
EXTENDS
    Naturals,
    FiniteSets

CONSTANTS
    CalculateHash(_,_,_),
    Hash,
    NoHashVal,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance,
    NoBlockVal

ASSUME
    /\ GenesisBalance \in Nat

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

Vars == <<hashFunction, lastHash, distributedLedger, received>>

\* View used by TLC when fingerprinting states: ignores hashFunction and lastHash
View == <<distributedLedger, received>>

-----------------------------------------------------------------------------

KeyPair ==
    CHOOSE mapping \in [PrivateKey -> PublicKey] :
        /\ \A key \in PublicKey :
            /\ \E privateKey \in PrivateKey :
                /\ mapping[privateKey] = key

Ownership ==
    CHOOSE mapping \in [Node -> PrivateKey] :
        /\ \A privateKey \in PrivateKey :
            /\ \E node \in Node :
                /\ mapping[node] = privateKey

N == INSTANCE Nano

-----------------------------------------------------------------------------

UndefinedHashesExist ==
    \E hash \in Hash : hashFunction[hash] = N!NoBlock

HashOf(block) ==
    IF \E hash \in Hash : hashFunction[hash] = block
    THEN CHOOSE hash \in Hash : hashFunction[hash] = block
    ELSE CHOOSE hash \in Hash : hashFunction[hash] = N!NoBlock

\* Model-level implementation of hash calculation, substituted for
\* CalculateHash in the model configuration.
CalculateHashImpl(block, oldLastHash, newLastHash) ==
    LET hash == HashOf(block) IN
    /\ newLastHash = hash
    /\ hashFunction' = [hashFunction EXCEPT ![hash] = block]

TypeInvariant ==
    /\ hashFunction \in [Hash -> N!Block \cup {N!NoBlock}]
    /\ N!TypeInvariant

SafetyInvariant ==
    /\ N!SafetyInvariant

Init ==
    /\ hashFunction = [hash \in Hash |-> N!NoBlock]
    /\ N!Init

StutterWhenHashesDepleted ==
    /\ UNCHANGED hashFunction
    /\ UNCHANGED lastHash
    /\ UNCHANGED distributedLedger
    /\ UNCHANGED received

Next ==
    IF UndefinedHashesExist
    THEN N!Next
    ELSE StutterWhenHashesDepleted

Spec ==
    /\ Init
    /\ [][Next]_Vars

THEOREM Safety == Spec => [](TypeInvariant /\ N!SafetyInvariant)

=============================================================================