------------------------------- MODULE RandomFunctionSampling -------------------------------

CONSTANTS 
    DOMAIN, CODOMAIN, SAMPLE_SIZE

VARIABLES 
    sampledFunctions

ASSUME 
    DOMAIN = {1..9},
    CODOMAIN = {0..9},
    SAMPLE_SIZE = 1000

Init == 
    /\ sampledFunctions \in SUBSET [DOMAIN -> CODOMAIN]
    /\ Cardinality(sampledFunctions) = SAMPLE_SIZE
    /\ sampledFunctions = RandomSubset([DOMAIN -> CODOMAIN], SAMPLE_SIZE)

Next == 
    /\ TRUE

Spec == 
    Init /\ [][Next]_<<sampledFunctions>>

Invariant == 
    /\ sampledFunctions \in SUBSET [DOMAIN -> CODOMAIN]
    /\ Cardinality(sampledFunctions) = SAMPLE_SIZE

THEOREM Spec => [] Invariant

=============================================================================