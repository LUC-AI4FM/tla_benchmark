---------------------------- MODULE SetAccumulate ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Data

VARIABLE state

vars == <<state>>

Init == state = {}

Next == \E d \in Data : state' = state \cup {d}

\* The description says the original file has no Spec. One is included here
\* because the output format requires it. It adds no fairness assumptions.
Spec == Init /\ [][Next]_vars

\* Type invariant (not stated in the description; included as a basic sanity check)
TypeOK == state \subseteq Data
=============================================================================