---- MODULE SimpleSetGrowth ----
EXTENDS FiniteSets

CONSTANT Data

VARIABLE state

Init == state = {}

Next == \E d \in Data : state' = state \cup {d}

Spec == Init /\ [][Next]_state

============================