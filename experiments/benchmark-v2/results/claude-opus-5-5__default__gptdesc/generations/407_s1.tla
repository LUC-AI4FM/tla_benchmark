---------------------------- MODULE PrintStateMachine ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

TypeOK ==
    /\ x \in {1, 2, 3}
    /\ y \in {1}

Init ==
    /\ x = 1
    /\ y = 1
    /\ PrintT("Init: x = 1, y = 1")

Assign ==
    /\ x' \in {1, 2, 3}
    /\ y' = 1
    /\ PrintT(<<"Generated state", x', y'>>)

Stutter ==
    UNCHANGED vars

Next ==
    \/ Assign
    \/ Stutter

\* The description mentions no temporal formula. This Spec is included only
\* because the required output format asks for one. It adds no fairness condition.
Spec == Init /\ [][Next]_vars

Inv == TRUE

=============================================================================