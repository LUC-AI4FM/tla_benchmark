---------------------------- MODULE DijkstraScholtenStub ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes

VARIABLES active, nodeColor, tokenPos, tokenColor

vars == <<active, nodeColor, tokenPos, tokenColor>>

Color == {"white", "black"}

TypeInvariant ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ nodeColor \in [Nodes -> Color]
    /\ tokenPos \in Nodes
    /\ tokenColor \in Color

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ nodeColor \in [Nodes -> Color]
    /\ tokenPos \in Nodes
    /\ tokenColor = "black"

Next ==
    /\ active' \in [Nodes -> BOOLEAN]
    /\ nodeColor' \in [Nodes -> Color]
    /\ tokenPos' \in Nodes
    /\ tokenColor' = "black"

Spec == Init /\ [][Next]_vars

===================================================================================