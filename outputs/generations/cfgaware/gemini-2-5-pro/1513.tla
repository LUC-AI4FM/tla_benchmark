---- MODULE SimpleStateMachine ----
EXTENDS TLC, FiniteSets

CONSTANT Nodes, Colors

VARIABLES active, color, token_pos, token_color

vars == <<active, color, token_pos, token_color>>

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ token_pos \in Nodes
    /\ token_color \in Colors

Init ==
    /\ token_pos \in Nodes
    /\ active = [n \in Nodes |-> (n = token_pos)]
    /\ color \in [Nodes -> Colors]
    /\ token_color \in Colors

\* The token moves to a different node. The new node becomes active,
\* and the old one becomes inactive.
MoveToken ==
    /\ \E new_pos \in Nodes:
        /\ new_pos # token_pos
        /\ token_pos' = new_pos
        /\ active' = [n \in Nodes |-> (n = new_pos)]
    /\ UNCHANGED <<color, token_color>>

\* The color of the node currently holding the token is changed.
ChangeNodeColor ==
    /\ \E new_node_color \in Colors:
        /\ color' = [color EXCEPT ![token_pos] = new_node_color]
    /\ UNCHANGED <<active, token_pos, token_color>>

\* The color of the token is changed.
ChangeTokenColor ==
    /\ \E new_token_color \in Colors:
        /\ token_color' = new_token_color
    /\ UNCHANGED <<active, color, token_pos>>

Next ==
    \/ MoveToken
    \/ ChangeNodeColor
    \/ ChangeTokenColor

Spec == Init /\ [][Next]_vars

================================