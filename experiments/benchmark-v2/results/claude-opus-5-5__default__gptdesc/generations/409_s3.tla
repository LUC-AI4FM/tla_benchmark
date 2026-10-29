---- MODULE SmallStateSpaceTest ----
EXTENDS Naturals, TLC

CONSTANTS Dummy

VARIABLES x

vars == <<x>>

Domain == 1..6
Range == 1..7

TypeOK == x \in [Domain -> Range]

Init == /\ Print("Starting exploration of function states", TRUE)
        /\ x \in [Domain -> Range]

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

Inv == TRUE

THEOREM Spec => [](TypeOK /\ Inv)
====