---- MODULE LargeInitStable ----
EXTENDS Naturals

VARIABLES x, y, z

vars == <<x, y, z>>

Init == /\ x \in 1..100
        /\ y \in 1..200
        /\ z \in 1..20

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in 1..100
          /\ y \in 1..200
          /\ z \in 1..20

Inv == TRUE

====