---- MODULE PrintStateMachine ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = 1
    /\ y = 1
    /\ PrintT("Init: x = 1, y = 1")

Next ==
    \/ /\ x' \in {1, 2, 3}
       /\ y' = 1
       /\ PrintT(<<"Generated state", x', y'>>)
    \/ UNCHANGED vars

Inv == TRUE

====