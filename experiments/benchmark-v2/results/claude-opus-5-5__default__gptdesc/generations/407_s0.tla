---- MODULE SmallPrint ----
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Init ==
    /\ x = 1
    /\ y = 1
    /\ PrintT("Init: initial state with x = 1 and y = 1")

Assign ==
    /\ x' \in {1, 2, 3}
    /\ y' = 1
    /\ PrintT(<<"Generated state", [x |-> x', y |-> y']>>)

Stutter ==
    UNCHANGED <<x, y>>

Next ==
    \/ Assign
    \/ Stutter

Inv == TRUE

Spec == Init /\ [][Next]_vars

====