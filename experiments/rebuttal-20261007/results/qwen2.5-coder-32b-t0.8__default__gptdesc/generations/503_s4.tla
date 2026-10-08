------------------------------ MODULE Consensus ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Values

VARIABLES chosen

Init == chosen = {}

Next ==
    \/ /\ chosen = {}
       /\ \E v \in Values : chosen' = {v}
    \/ /\ chosen /= {}
       /\ chosen' = chosen

Spec == Init /\ [][Next]_<<chosen>>

\* Safety property: at most one value is ever chosen
Inv == Cardinality(chosen) <= 1

\* Liveness property: eventually some value is chosen
WF == WF_next(<<chosen>>)

THEOREM Spec => []Inv

=============================================================================