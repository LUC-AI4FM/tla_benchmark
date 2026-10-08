------------------------------- MODULE Consensus -------------------------------
EXTENDS Integers

CONSTANTS Values

VARIABLES chosen

Init == chosen = {}

Next ==
    \/ /\ chosen = {}
       /\ \E v \in Values : chosen' = {v}
    \/ chosen' = chosen

Spec ==
    /\ Init
    /\ [][Next]_<<chosen>>
    /\ WF_next(Next)

\* Safety property: at most one value is ever chosen
Inv == Cardinality(chosen) <= 1

THEOREM Inv \A <<chosen>> \in Spec

=============================================================================