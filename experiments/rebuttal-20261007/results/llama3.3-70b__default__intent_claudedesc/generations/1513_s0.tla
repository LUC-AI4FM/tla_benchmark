```
MODULE DijkstraScholtenToken
EXTENDS Integers, FiniteSets

CONSTANTS Nodes
VARIABLES nodeActivity, nodeColors, tokenPosition, tokenColor

Init ==
  /\ nodeActivity \in [Nodes -> BOOLEAN]
  /\ nodeColors \in [Nodes -> {"white", "black"}]
  /\ tokenPosition \in Nodes
  /\ tokenColor = "black"

Next ==
  /\ nodeActivity' \in [Nodes -> BOOLEAN]
  /\ nodeColors' \in [Nodes -> {"white", "black"}]
  /\ tokenPosition' \in Nodes
  /\ tokenColor' = "black"

TypeInvariant ==
  /\ nodeActivity \in [Nodes -> BOOLEAN]
  /\ nodeColors \in [Nodes -> {"white", "black"}]
  /\ tokenPosition \in Nodes
  /\ tokenColor = "black"

Spec == Init /\ [][Next]_<<nodeActivity, nodeColors, tokenPosition, tokenColor>>
THEOREM Spec => []TypeInvariant
```