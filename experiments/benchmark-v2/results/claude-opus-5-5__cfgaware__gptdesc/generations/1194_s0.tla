---- MODULE LargeStateSpace ----
EXTENDS Naturals

VARIABLES x, y, z

vars == <<x, y, z>>

Init ==
    /\ x \in 0..999
    /\ y \in 0..999
    /\ z \in 0..99

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TRUE

====