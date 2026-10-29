---------------------------- MODULE SetAccumulator ----------------------------
EXTENDS Naturals, FiniteSets

\* The data set from which elements are drawn
Data == 1..3

VARIABLES state

vars == << state >>

\* Type invariant
TypeOK == state \subseteq Data

\* Initial condition: state starts as the empty set
Init == state = {}

\* Next-state action: nondeterministically add an element of Data to state
Next == \E d \in Data : state' = state \cup {d}

\* Temporal specification (no fairness assumptions)
Spec == Init /\ [][Next]_vars

=============================================================================