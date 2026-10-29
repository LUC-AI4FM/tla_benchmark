---------------------------- MODULE PrintStateMachine ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = 1
    /\ y = 1
    /\ PrintT(<<"Init", "x", x, "y", y>>)

Assign ==
    /\ x' \in {1, 2, 3}
    /\ y' = 1
    /\ PrintT(<<"Next", "x'", x', "y'", y'>>)

Stutter ==
    UNCHANGED <<x, y>>

Next ==
    \/ Assign
    \/ Stutter

Inv == TRUE

TypeOK ==
    /\ x \in {1, 2, 3}
    /\ y = 1

Spec == Init /\ [][Next]_vars

=============================================================================