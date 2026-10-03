------------------------------- MODULE SimpleStateMachine ------------------------------

CONSTANTS 
    Nodes, Colors

VARIABLES 
    nodeActivityStatus, nodeColors, tokenPosition, tokenColor

ASSUME 
    \A n \in Nodes : nodeActivityStatus[n] \in BOOLEAN /\ nodeColors[n] \in Colors
    tokenPosition \in Nodes
    tokenColor \in Colors

Init == 
    \E na \in [Nodes -> BOOLEAN], nc \in [Nodes -> Colors], tp \in Nodes, tc \in Colors :
        (\A n \in Nodes : na[n] = FALSE) /\  (* Initially all nodes are inactive *)
        (\A n \in Nodes : nc[n] = <<Colors>>[1]) /\  (* Initially all nodes have the first color *)
        tp = <<Nodes>>[1] /\  (* Token starts at the first node *)
        tc = <<Colors>>[1] /\  (* Token starts with the first color *)
        nodeActivityStatus' = na /\ 
        nodeColors' = nc /\ 
        tokenPosition' = tp /\ 
        tokenColor' = tc

Next == 
    \/ \E n \in Nodes, c \in Colors :
        (nodeActivityStatus[tokenPosition] = TRUE) /\  (* Token can only move if the current node is active *)
        (tokenPosition' = n) /\  (* Move token to another node *)
        (tokenColor' = c) /\  (* Change token color *)
        (nodeColors' = [nodeColors EXCEPT ![n] = c]) /\  (* Update the color of the new node where the token lands *)
        (UNION {S \in SUBSET Nodes : S /= {}} : (\A m \in S : nodeActivityStatus'[m] = nodeActivityStatus[m]))  (* Other nodes' activity status remains unchanged *)
    \/ \E n \in Nodes :
        (nodeActivityStatus[n] = FALSE) /\  (* Activate a node *)
        (nodeActivityStatus' = [nodeActivityStatus EXCEPT ![n] = TRUE]) /\  (* Update the activity status of the node *)
        (UNION {S \in SUBSET Nodes : S /= {}} : (\A m \in S : m # n => nodeColors'[m] = nodeColors[m])) /\  (* Other nodes' colors remain unchanged *)
        (tokenPosition' = tokenPosition) /\ 
        (tokenColor' = tokenColor)

Spec == Init /\ [][Next]_<<nodeActivityStatus, nodeColors, tokenPosition, tokenColor>>

=============================================================================