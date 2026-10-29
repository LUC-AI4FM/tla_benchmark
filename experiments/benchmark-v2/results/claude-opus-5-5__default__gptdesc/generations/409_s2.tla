---- MODULE SmallStateSpaceTest ----
EXTENDS Naturals, TLC

VARIABLE x

vars == <<x>>

Init ==
    /\ Print("Computing initial states", TRUE)
    /\ x \in [1..6 -> 1..7]

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

Inv == TRUE

TypeOK == x \in [1..6 -> 1..7]

====