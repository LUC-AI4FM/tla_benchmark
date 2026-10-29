---- MODULE LargeInitialStateSpace ----
EXTENDS Naturals

VARIABLES x, y, z

vars == <<x, y, z>>

Init ==
    /\ x \in 1..10000
    /\ y \in 1..10000
    /\ z \in 1..10000

Next ==
    /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TRUE

TypeOK ==
    /\ x \in 1..10000
    /\ y \in 1..10000
    /\ z \in 1..10000

THEOREM Spec => []Inv
====