---------------------------- MODULE TLCStateGenTest ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ PrintT("Expect 3 distinct states to be generated from the initial state")
    /\ x = 1
    /\ y = 1

GenerateNext ==
    /\ x' \in {1, 2, 3}
    /\ y' = 1
    /\ PrintT(<<"Generated state", x', y'>>)

Stutter ==
    UNCHANGED <<x, y>>

Next ==
    \/ GenerateNext
    \/ Stutter

Spec == Init /\ [][Next]_vars

Inv == TRUE

TypeOK ==
    /\ x \in {1, 2, 3}
    /\ y = 1

=============================================================================