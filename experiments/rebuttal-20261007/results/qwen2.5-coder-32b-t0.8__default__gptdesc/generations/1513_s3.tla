------------------------------ MODULE SimpleStateMachine ------------------------------

EXTENDS TLC, Integers

CONSTANTS 
    Nodes,          \* A finite set of nodes
    Colors          \* A two-element set representing colors

VARIABLES 
    activityStatus, \* A function mapping each node to its activity status (TRUE or FALSE)
    nodeColors,     \* A function mapping each node to a color from the Colors set
    tokenPosition,  \* The current position of the token, an element of Nodes
    tokenColor      \* The color of the token, an element of Colors

Init == 
    /\ activityStatus \in [Nodes -> BOOLEAN]
    /\ nodeColors \in [Nodes -> Colors]
    /\ tokenPosition \in Nodes
    /\ tokenColor \in Colors

Next ==
    \/ \/ \E n \in Nodes : 
            \/ \/ activityStatus' = [activityStatus EXCEPT ![n] = ~activityStatus[n]]
                /\ nodeColors' = nodeColors
                /\ tokenPosition' = tokenPosition
                /\ tokenColor' = tokenColor
            \/ /\ activityStatus' = activityStatus
                /\ nodeColors' = [nodeColors EXCEPT ![n] = CHOOSE c \in Colors : c # nodeColors[n]]
                /\ tokenPosition' = tokenPosition
                /\ tokenColor' = tokenColor
        \/ \E n \in Nodes : 
            tokenPosition' = n
            /\ activityStatus' = activityStatus
            /\ nodeColors' = nodeColors
            /\ tokenColor' = CHOOSE c \in Colors : c # tokenColor

Spec ==
    Init /\ [][Next]_<<activityStatus, nodeColors, tokenPosition, tokenColor>>

=============================================================================