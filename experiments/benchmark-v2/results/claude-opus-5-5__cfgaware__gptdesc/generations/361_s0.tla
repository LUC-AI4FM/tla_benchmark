---- MODULE LargeInitStates ----
EXTENDS Naturals

VARIABLES x, y, z

vars == <<x, y, z>>

Init == /\ x \in 1..1000
        /\ y \in 1..1000
        /\ z \in 1..100

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv == TRUE
====