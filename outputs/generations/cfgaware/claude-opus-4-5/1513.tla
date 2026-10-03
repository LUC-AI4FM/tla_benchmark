---------------------------- MODULE spec ----------------------------

EXTENDS Naturals

CONSTANTS Nodes, Colors

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ tpos \in Nodes
    /\ tcolor \in Colors

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ tpos \in Nodes
    /\ tcolor \in Colors

Next ==
    /\ active' \in [Nodes -> BOOLEAN]
    /\ color' \in [Nodes -> Colors]
    /\ tpos' \in Nodes
    /\ tcolor' \in Colors

Spec == Init /\ [][Next]_vars

=============================================================================