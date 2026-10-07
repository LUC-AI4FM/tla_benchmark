------------------------------- MODULE M -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes
VARIABLES active, color, tpos, tcolor

Init == /\ active \in [Nodes -> BOOLEAN]
        /\ color \in [Nodes -> {"white", "black"}]
        /\ tpos \in Nodes
        /\ tcolor = "black"
        /\ \/ active[23] \/ active[42] \/ active[56]

Next == /\ active' \in [Nodes -> BOOLEAN]
        /\ color' \in [Nodes -> {"white", "black"}]
        /\ tpos' \in Nodes
        /\ tcolor' = "black"
        /\ \/ active'[23] \/ active'[42] \/ active'[56]

Spec == Init /\ [][Next]_<<active, color, tpos, tcolor>>
=============================================================================