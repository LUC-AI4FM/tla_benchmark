```
MODULE SimpleStateMachine
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Colors
VARIABLES activityStatus, nodeColors, tokenPosition, tokenColor

Init ==
  /\ activityStatus \in [Nodes -> {<<true>, <false>>}]
  /\ nodeColors \in [Nodes -> Colors]
  /\ tokenPosition \in Nodes
  /\ tokenColor \in Colors

Next ==
  /\ activityStatus' = [activityStatus EXCEPT ![tokenPosition] = <<true>]
  /\ nodeColors' = IF (tokenColor = "Red") THEN [nodeColors EXCEPT ![tokenPosition] = "Blue"] ELSE nodeColors
  /\ tokenPosition' \in Nodes
  /\ tokenColor' = IF (nodeColors[tokenPosition'] = "Red") THEN "Blue" ELSE "Red"

Spec ==
  Init /\ [][Next]_vars

THEOREM Spec => []Init
```