```
MODULE SimpleStateMachine
EXTENDS Integers, FiniteSets

CONSTANTS NodeSet, ColorSet
ASSUME NodeSet \subseteq 1..4
ASSUME ColorSet = {"red", "green"}

VARIABLES nodeActivityStatus, 
          nodeColors, 
          tokenPosition, 
          tokenColor

Init ==
  /\ nodeActivityStatus \in [NodeSet -> {<<"active">>, <<"inactive">>}]
  /\ nodeColors \in [NodeSet -> ColorSet]
  /\ tokenPosition \in NodeSet
  /\ tokenColor \in ColorSet
  /\ \A n \in NodeSet : 
      (nodeActivityStatus[n] = <<"active">>) => (nodeColors[n] = "green")

Next ==
  /\ nodeActivityStatus' \in [NodeSet -> {<<"active">>, <<"inactive">>}]
  /\ nodeColors' \in [NodeSet -> ColorSet]
  /\ tokenPosition' \in NodeSet
  /\ tokenColor' \in ColorSet
  /\ \A n \in NodeSet : 
      (nodeActivityStatus[n] = <<"active">>) => (nodeColors'[n] = "green")
  /\ tokenPosition' = IF tokenPosition = Max(NodeSet) THEN Min(NodeSet) ELSE tokenPosition + 1

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Init
```