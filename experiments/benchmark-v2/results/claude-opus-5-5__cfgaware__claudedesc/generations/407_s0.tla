---- MODULE Test ----
EXTENDS Naturals, TLC

VARIABLES x, y

Init ==
    /\ PrintT("Should find exactly three distinct states")
    /\ x = 1
    /\ y = 1

Next ==
    \/ /\ x' \in {1, 2, 3}
       /\ y' = 1
       /\ PrintT(<<"Generated state", x', y'>>)
    \/ UNCHANGED <<x, y>>

Inv == TRUE

====