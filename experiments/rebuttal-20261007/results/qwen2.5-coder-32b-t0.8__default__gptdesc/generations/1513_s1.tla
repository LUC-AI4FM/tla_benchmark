----------------------------- MODULE StateMachine -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS 
    Nodes,  \* A finite set of nodes
    Colors  \* A set containing exactly two colors

VARIABLES 
    activityStatus, \* Maps each node to a boolean indicating if it is active
    nodeColors,     \* Maps each node to a color
    tokenPosition,  \* The position of the token (must be in Nodes)
    tokenColor      \* The color of the token

Init == 
    /\ activityStatus \in [Nodes -> BOOLEAN]
    /\ nodeColors \in [Nodes -> Colors]
    /\ tokenPosition \in Nodes
    /\ tokenColor \in Colors

Next ==
    \/ \E n \in Nodes, a \in BOOLEAN : 
        (/\ tokenPosition' = n
         /\ tokenColor' = nodeColors[n]
         /\ activityStatus' = [activityStatus EXCEPT ![n] = a])
    \/ \E n \in Nodes :
        (/\ tokenPosition' = n
         /\ tokenColor' = Colors \ {nodeColors[tokenPosition]}
         /\ activityStatus' = activityStatus)

Spec == 
    WF_vars(Init, Next)
    
vars == <<activityStatus, nodeColors, tokenPosition, tokenColor>>

=============================================================================