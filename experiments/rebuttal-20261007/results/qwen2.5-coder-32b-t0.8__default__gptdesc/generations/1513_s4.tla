------------------------------- MODULE SimpleStateMachine -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Colors
ASSUME Nodes \in SUBSET Nat /\ Cardinality(Nodes) = 4
ASSUME Colors = {"red", "blue"}

VARIABLES nodeActivityStatus, nodeColors, tokenPosition, tokenColor

Init == 
    /\ nodeActivityStatus \in [Nodes -> BOOLEAN]
    /\ nodeColors \in [Nodes -> Colors]
    /\ tokenPosition \in Nodes
    /\ tokenColor \in Colors

Next ==
    \/ \E n \in Nodes: nodeActivityStatus' = [nodeActivityStatus EXCEPT ![n] = ~nodeActivityStatus[n]]
       /\ nodeColors' = nodeColors 
       /\ tokenPosition' = tokenPosition 
       /\ tokenColor' = tokenColor
    \/ \E c \in Colors: nodeActivityStatus' = nodeActivityStatus 
       /\ nodeColors' = [nodeColors EXCEPT ![tokenPosition] = c]
       /\ tokenPosition' = tokenPosition 
       /\ tokenColor' = tokenColor
    \/ \E n \in Nodes: nodeActivityStatus' = nodeActivityStatus 
       /\ nodeColors' = nodeColors 
       /\ tokenPosition' = n 
       /\ tokenColor' = tokenColor
    \/ \E c \in Colors: nodeActivityStatus' = nodeActivityStatus 
       /\ nodeColors' = nodeColors 
       /\ tokenPosition' = tokenPosition 
       /\ tokenColor' = c

Spec == Init /\ [][Next]_<<nodeActivityStatus, nodeColors, tokenPosition, tokenColor>>

================================================================================