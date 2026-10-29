---------------------------- MODULE SmallStateSpaceTest ----------------------------
EXTENDS Naturals, TLC

CONSTANTS N, M

ASSUME N = 6 /\ M = 7

VARIABLES x

vars == <<x>>

Domain == 1..6
Range  == 1..7

FunSet == [Domain -> Range]

TypeOK == x \in FunSet

Init ==
    /\ PrintT("Init: starting exploration of [1..6 -> 1..7]")
    /\ x \in FunSet

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

Inv == TRUE

THEOREM Spec => []Inv
=============================================================================