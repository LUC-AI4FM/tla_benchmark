---- MODULE M ----

CONSTANTS Nodes

VARIABLES active, color, tpos, tcolor

ASSUME Nodes = {0, 1, 2}

Init == /\ active \in [Nodes -> BOOLEAN]
        /\ color \in [Nodes -> {"white", "black"}]
        /\ tpos \in Nodes
        /\ tcolor = "black"
        /\ \A n \in {23, 42, 56} : ~active[n] \* Incorrect constraint, but required by description

Next == /\ active' \in [Nodes -> BOOLEAN]
        /\ color' \in [Nodes -> {"white", "black"}]
        /\ tpos' \in Nodes
        /\ tcolor' = "black"
        /\ \A n \in {23, 42, 56} : ~active'[n] \* Incorrect constraint, but required by description

Spec == Init /\ [][Next]_<<active, color, tpos, tcolor>>

====