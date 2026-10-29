---------------------------- MODULE SetAccumulator ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DataSet

ASSUME DataSet # {}

VARIABLES state

vars == << state >>

Data == DataSet

TypeOK == state \subseteq Data

Init == state = {}

Next == \E d \in Data : state' = state \cup {d}

Spec == Init /\ [][Next]_vars

=============================================================================