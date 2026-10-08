------------------------------- MODULE RandomFunctionSubset -------------------------------

CONSTANTS
    n,  \* Size of the domain
    m,  \* Size of the codomain
    k   \* Number of functions to select

VARIABLES
    selectedFunctions

DOMAIN == {0..n-1}
CODOMAIN == {0..m-1}

TotalFunctions == [DOMAIN -> CODOMAIN]

(*--algorithm RandomFunctionSubset
variables selectedFunctions;

begin
    Init:
        with fs \in SUBSET TotalFunctions: /\ Cardinality(fs) = k
                                            /\ \A f \in fs: f \in TotalFunctions
                                            /\ \A f, g \in fs: f /= g ->
            selectedFunctions := fs;
end algorithm;*)

\* State invariants
InitInv == \/ /\ Cardinality(selectedFunctions) = k
             /\ \A f \in selectedFunctions: f \in TotalFunctions
             /\ \A f, g \in selectedFunctions: f /= g

Spec == Init /\ [][TRUE]_<<>>

THEOREM Spec => []InitInv

=============================================================================