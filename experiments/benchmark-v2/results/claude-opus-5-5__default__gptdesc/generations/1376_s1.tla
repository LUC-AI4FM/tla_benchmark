---------------------------- MODULE SetAccumulator ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES state

vars == << state >>

Data == 1..3

Init == state = {}

Next == \E d \in Data : state' = state \cup {d}

Spec == Init /\ [][Next]_vars

TypeOK == state \subseteq Data

=============================================================================