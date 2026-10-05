---------------------------- MODULE M ----------------------------

EXTENDS Integers

CONSTANT Nodes

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> {"white", "black"}]
    /\ tpos \in Nodes
    /\ tcolor \in {"white", "black"}

Init ==
    /\ active \in [{23, 42, 56} -> BOOLEAN]
    /\ color \in [Nodes -> {"white", "black"}]
    /\ tpos \in Nodes
    /\ tcolor = "black"

Next ==
    /\ active' \in [{23, 42, 56} -> BOOLEAN]
    /\ color' \in [Nodes -> {"white", "black"}]
    /\ tpos' \in Nodes
    /\ tcolor' = "black"

Spec == Init /\ [][Next]_vars

=================================================================