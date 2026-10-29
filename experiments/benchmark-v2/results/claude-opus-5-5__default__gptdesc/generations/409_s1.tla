---- MODULE SmallStateSpaceTest ----
EXTENDS Naturals, TLC

CONSTANTS Dom, Rng

ASSUME Dom = 1..6 /\ Rng = 1..7

VARIABLES x

vars == << x >>

FunSet == [1..6 -> 1..7]

TypeOK == x \in FunSet

Init == /\ Print("Starting to enumerate initial states of [1..6 -> 1..7]", TRUE)
        /\ x \in FunSet

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

Inv == TRUE

THEOREM Spec => []Inv
====