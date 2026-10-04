---------------------------- MODULE StateColorToken ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Colors

ASSUME Nodes # {} /\ Colors # {}

VARIABLES active, color, tokenPos, tokenColor

vars == <<active, color, tokenPos, tokenColor>>

TypeOK ==
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

================================================================================