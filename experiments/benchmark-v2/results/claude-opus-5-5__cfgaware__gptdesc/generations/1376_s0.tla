---- MODULE SetAccumulate ----
EXTENDS Naturals

VARIABLE state

Data == {1, 2, 3}

Init == state = {}

Next == \E d \in Data : state' = state \cup {d}

====