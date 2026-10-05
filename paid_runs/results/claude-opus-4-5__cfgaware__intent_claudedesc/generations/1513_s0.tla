---------------------------- MODULE DijkstraScholten ----------------------------

EXTENDS Integers

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Nodes == 0..(N-1)

Color == {"white", "black"}

VARIABLES active, color, tokenPos, tokenColor

vars == <<active, color, tokenPos, tokenColor>>

TypeInvariant ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ tokenPos \in Nodes
    /\ tokenColor \in Color

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Color]
    /\ tokenPos \in Nodes
    /\ tokenColor = "black"

Next ==
    /\ active' \in [Nodes -> BOOLEAN]
    /\ color' \in [Nodes -> Color]
    /\ tokenPos' \in Nodes
    /\ tokenColor' = "black"

Spec == Init /\ [][Next]_vars

=============================================================================