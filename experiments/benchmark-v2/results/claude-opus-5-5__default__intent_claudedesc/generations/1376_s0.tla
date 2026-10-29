---- MODULE GrowingSet ----
EXTENDS Naturals, FiniteSets

CONSTANTS D1, D2

Data == {D1, D2}

VARIABLE set

vars == <<set>>

TypeOK == set \subseteq Data

Init == set = {}

Add(d) == set' = set \cup {d}

Next == \E d \in Data : Add(d)

Spec == Init /\ [][Next]_vars

Monotonic == [][set \subseteq set']_vars

THEOREM Spec => []TypeOK
====