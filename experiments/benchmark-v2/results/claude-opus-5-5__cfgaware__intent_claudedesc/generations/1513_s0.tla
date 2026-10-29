---- MODULE EWD840Stub ----
EXTENDS Naturals

N == 3

Nodes == 0 .. N - 1

Color == {"white", "black"}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ tpos \in Nodes
    /\ tcolor \in Color

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ tpos \in Nodes
    /\ tcolor = "black"

Next ==
    /\ active' \in [Nodes -> BOOLEAN]
    /\ color' \in [Nodes -> Color]
    /\ tpos' \in Nodes
    /\ tcolor' = "black"

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
====