------------------------------- MODULE RandomFunctionSubset -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS n, m, k

VARIABLES selectedFunctions

DOMAIN == {0..n-1}
CODOMAIN == {0..m-1}

TotalFunctions == [DOMAIN -> CODOMAIN]

Init == /\ selectedFunctions \in SUBSET TotalFunctions
        /\ Cardinality(selectedFunctions) = k
        /\ \A f \in selectedFunctions: f \in [DOMAIN -> CODOMAIN]
        /\ \A f, g \in selectedFunctions: f /= g

Next == FALSE

Spec == Init /\ [][\E<<>> \in _]

(* Fairness conditions are not applicable as there is no further state change after initialization *)
=============================================================================================