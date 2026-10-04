---------------------------- MODULE StateToken ----------------------------
EXTENDS Naturals

CONSTANTS Nodes, Colors

VARIABLES active, color, tokenPos, tokenColor

vars == <<active, color, tokenPos, tokenColor>>

TypeInvariant ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ tokenPos \in Nodes
    /\ tokenColor \in Colors

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ tokenPos \in Nodes
    /\ tokenColor \in Colors

Next ==
    /\ active' \in [Nodes -> BOOLEAN]
    /\ color' \in [Nodes -> Colors]
    /\ tokenPos' \in Nodes
    /\ tokenColor' \in Colors

Spec == Init /\ [][Next]_vars

=============================================================================