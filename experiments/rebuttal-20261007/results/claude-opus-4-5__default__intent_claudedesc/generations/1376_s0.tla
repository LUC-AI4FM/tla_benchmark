---------------------------- MODULE GrowingSet ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Data

VARIABLES set

vars == <<set>>

TypeOK == set \subseteq Data

Init == set = {}

Add(d) == 
    /\ d \in Data
    /\ d \notin set
    /\ set' = set \cup {d}

Next == 
    \/ \E d \in Data : Add(d)
    \/ (set = Data /\ UNCHANGED set)

Spec == Init /\ [][Next]_vars

MonotonicallyGrowing == [][set \subseteq set']_vars

=============================================================================