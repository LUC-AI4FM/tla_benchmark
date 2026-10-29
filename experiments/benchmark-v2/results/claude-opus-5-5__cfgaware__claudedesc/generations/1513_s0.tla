---- MODULE M ----
EXTENDS Naturals

Nodes == 0..2

Color == {"white", "black"}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ tpos \in Nodes
    /\ tcolor \in Color

Init ==
    /\ active \in [{23, 42, 56} -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ tpos \in Nodes
    /\ tcolor = "black"

Next ==
    /\ active' \in [{23, 42, 56} -> BOOLEAN]
    /\ color' \in [Nodes -> Color]
    /\ tpos' \in Nodes
    /\ tcolor' = "black"

Spec == Init /\ [][Next]_vars

====