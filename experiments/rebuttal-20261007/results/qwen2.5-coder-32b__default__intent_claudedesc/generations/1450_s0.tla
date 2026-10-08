------------------------------- MODULE RandomFunctionSample -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS 
    DOMAIN, CODOMAIN, SAMPLE_SIZE

VARIABLES selectedFunctions

Init == /\ selectedFunctions = {}
        /\ selectedFunctions \in SUBSET [DOMAIN -> CODOMAIN]
        /\ Cardinality(selectedFunctions) = 0

Next == /\ selectedFunctions' = CHOOSE s \in RandomSubset([DOMAIN -> CODOMAIN], SAMPLE_SIZE) : TRUE
        /\ UNCHANGED <<>>

Spec == Init /\ [][Next]_<<selectedFunctions>>

Invariant == TRUE

=============================================================================