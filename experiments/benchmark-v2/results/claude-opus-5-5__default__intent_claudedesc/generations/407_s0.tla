---------------------------- MODULE PrintStates ----------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = 1
    /\ y = 1
    /\ PrintT(<<"Init", "x", 1, "y", 1>>)

Stutter ==
    /\ PrintT(<<"Stutter from", "x", x, "y", y>>)
    /\ UNCHANGED vars

Assign ==
    /\ \E v \in {1, 2, 3} :
          /\ PrintT(<<"Assign from", "x", x, "y", y, "to x'", v>>)
          /\ x' = v
    /\ y' = 1
    /\ PrintT(<<"Generated state", "x'", x', "y'", y'>>)

Next ==
    \/ Stutter
    \/ Assign

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in {1, 2, 3}
    /\ y = 1

Inv == TRUE

=============================================================================