---------------------------- MODULE StateToken ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Colors

ASSUME Nodes # {} /\ Cardinality(Nodes) > 0
ASSUME Colors = {"white", "black"}

VARIABLES active, color, token, tcolor

vars == <<active, color, token, tcolor>>

TypeInvariant ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ token \in Nodes
    /\ tcolor \in Colors

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ token \in Nodes
    /\ tcolor \in Colors

Next ==
    /\ active' \in [Nodes -> BOOLEAN]
    /\ color' \in [Nodes -> Colors]
    /\ token' \in Nodes
    /\ tcolor' \in Colors

Spec == Init /\ [][Next]_vars

=============================================================================