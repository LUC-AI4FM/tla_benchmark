---------------------------- MODULE PrintStateMachine ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

TypeOK ==
    /\ x \in {1, 2, 3}
    /\ y = 1

Init ==
    /\ x = 1
    /\ y = 1
    /\ PrintT("Init: x = 1, y = 1")

Step ==
    /\ x' \in {1, 2, 3}
    /\ y' = 1
    /\ PrintT(<<"Generated state", x', y'>>)

Stutter ==
    UNCHANGED vars

Next ==
    \/ Step
    \/ Stutter

Inv == TRUE

Spec == Init /\ [][Next]_vars

=============================================================================