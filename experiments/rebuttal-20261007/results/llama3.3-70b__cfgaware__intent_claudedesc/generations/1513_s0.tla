---------------------------- MODULE DijkstraScholtenStub ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Nodes
VARIABLES nodeActive, nodeColor, tokenPosition, tokenColor

TypeInvariant == 
  /\ nodeActive \in [Nodes -> BOOLEAN]
  /\ nodeColor \in [Nodes -> {"white", "black"}]
  /\ tokenPosition \in Nodes
  /\ tokenColor = "black"

Init == 
  /\ nodeActive \in [Nodes -> BOOLEAN]
  /\ nodeColor \in [Nodes -> {"white", "black"}]
  /\ tokenPosition \in Nodes
  /\ tokenColor = "black"

Next == 
  /\ nodeActive' \in [Nodes -> BOOLEAN]
  /\ nodeColor' \in [Nodes -> {"white", "black"}]
  /\ tokenPosition' \in Nodes
  /\ tokenColor' = "black"

Spec == Init /\ [][Next]_<<nodeActive, nodeColor, tokenPosition, tokenColor>>

THEOREM Spec => []TypeInvariant
=============================================================================