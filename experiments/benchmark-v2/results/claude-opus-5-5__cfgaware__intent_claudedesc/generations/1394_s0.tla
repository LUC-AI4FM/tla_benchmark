---------------------------- MODULE UnchangedSubst ----------------------------
EXTENDS Naturals

VARIABLES x, y

C == 1

---------------------------- MODULE Inner ----------------------------
EXTENDS Naturals

VARIABLES a, b, c

vars == <<a, b, c>>

Init ==
    /\ a \in {0, 1}
    /\ b \in {0, 1}
    /\ c \in {0, 1}

Next ==
    /\ a < 3
    /\ a' = a + 1
    /\ UNCHANGED <<b, c>>

Spec == Init /\ [][Next]_vars
=============================================================================