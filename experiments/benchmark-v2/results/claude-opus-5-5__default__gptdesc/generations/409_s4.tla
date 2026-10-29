---- MODULE SmallStateSpaceTest ----
EXTENDS Naturals, TLC

VARIABLE x

vars == <<x>>

Init == /\ PrintT("Computing initial states")
        /\ x \in [1..6 -> 1..7]

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

Inv == TRUE

TypeOK == x \in [1..6 -> 1..7]
====