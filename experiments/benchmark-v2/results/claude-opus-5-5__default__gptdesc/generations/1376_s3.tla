---------------------------- MODULE SetAccumulate ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Elem1, Elem2, Elem3

VARIABLE state

vars == << state >>

\* The data set from which elements are drawn
Data == {Elem1, Elem2, Elem3}

\* Initially the state is the empty set
Init == state = {}

\* Each step nondeterministically adds one element of Data to state
Next == \E d \in Data : state' = state \cup {d}

\* Temporal specification (no fairness assumptions)
Spec == Init /\ [][Next]_vars

\* Type invariant: state is always a subset of Data
TypeOK == state \subseteq Data

=============================================================================