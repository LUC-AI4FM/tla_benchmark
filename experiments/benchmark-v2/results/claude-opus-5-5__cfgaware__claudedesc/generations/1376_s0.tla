---- MODULE Github407 ----
EXTENDS Naturals, FiniteSets

Data == {"d1", "d2"}

VARIABLE state

vars == <<state>>

Init == state = {}

Next == \E d \in Data : state' = state \cup {d}

Spec == Init /\ [][Next]_vars

TypeOK == state \subseteq Data
====