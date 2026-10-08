------------------------------- MODULE SimpleStateMachine -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Colors
ASSUME Cardinality(Nodes) = 4 /\ Cardinality(Colors) = 2

VARIABLES nodeActivityStatus, nodeColors, tokenPosition, tokenColor

Init == 
    /\ nodeActivityStatus \in [Nodes -> BOOLEAN]
    /\ nodeColors \in [Nodes -> Colors]
    /\ tokenPosition \in Nodes
    /\ tokenColor \in Colors

Next ==
    \/ /\ tokenPosition' = tokenPosition
       /\ tokenColor' = tokenColor
       /\ nodeActivityStatus' = nodeActivityStatus
       /\ nodeColors' = nodeColors
    \/ /\ tokenPosition' \in Nodes
       /\ tokenColor' \in Colors
       /\ nodeActivityStatus' \in [Nodes -> BOOLEAN]
       /\ nodeColors' \in [Nodes -> Colors]

Spec ==
    Init /\ [][Next]_<<nodeActivityStatus, nodeColors, tokenPosition, tokenColor>>

=======================================================================================