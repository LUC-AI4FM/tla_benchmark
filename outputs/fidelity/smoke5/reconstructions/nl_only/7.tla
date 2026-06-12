---- MODULE SubmoduleTest ----
EXTENDS Naturals

CONSTANTS C
VARIABLES v

---- MODULE InnerModule1 ----
InnerOp1 == FALSE
====

---- MODULE InnerModule2 ----
InnerOp2 == FALSE
====

Op == FALSE

Init == TRUE

Next == UNCHANGED v

Spec == Init /\ [][Next]_v

====