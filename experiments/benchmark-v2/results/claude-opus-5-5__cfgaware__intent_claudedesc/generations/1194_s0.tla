---- MODULE LargeInitStates ----
EXTENDS Naturals

VARIABLES x, y, z

vars == <<x, y, z>>

Init ==
    /\ x \in 0..99
    /\ y \in 0..49
    /\ z \in 0..99

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TRUE

====