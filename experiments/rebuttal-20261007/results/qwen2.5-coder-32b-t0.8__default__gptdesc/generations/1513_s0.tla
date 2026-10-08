------------------------------- MODULE SimpleStateMachine -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Colors

VARIABLES nodeActivity, nodeColors, tokenPosition, tokenColor

Init == 
  /\ nodeActivity \in [Nodes -> BOOLEAN]
  /\ nodeColors \in [Nodes -> Colors]
  /\ tokenPosition \in Nodes
  /\ tokenColor \in Colors

Next ==
  /\ \E newTokenPos \in Nodes : tokenPosition' = newTokenPos
  /\ \E newTokenCol \in Colors : tokenColor' = newTokenCol
  /\ nodeActivity' \in [Nodes -> BOOLEAN]
  /\ nodeColors' \in [Nodes -> Colors]

Spec == Init /\ [][Next]_<<nodeActivity, nodeColors, tokenPosition, tokenColor>>

=======================================================================================