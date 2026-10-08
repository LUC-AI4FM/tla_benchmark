```
MODULE SimpleStateMachine
EXTENDS Integers, FiniteSets

CONSTANTS NodeSet, ColorDomain
VARIABLES nodeActivityStatus, nodeColors, tokenPosition, tokenColor

Init ==
  /\ nodeActivityStatus \in [NodeSet -> {<<"active">>, <<"inactive">>}]
  /\ nodeColors \in [NodeSet -> ColorDomain]
  /\ tokenPosition \in NodeSet
  /\ tokenColor \in ColorDomain
  /\ DOMAIN nodeActivityStatus = NodeSet
  /\ DOMAIN nodeColors = NodeSet

Next ==
  /\ nodeActivityStatus' \in [NodeSet -> {<<"active">>, <<"inactive">>}]
  /\ nodeColors' \in [NodeSet -> ColorDomain]
  /\ tokenPosition' \in NodeSet
  /\ tokenColor' \in ColorDomain
  /\ DOMAIN nodeActivityStatus' = NodeSet
  /\ DOMAIN nodeColors' = NodeSet
  /\ (nodeActivityStatus = nodeActivityStatus') \/ (nodeActivityStatus' = [n \in NodeSet |-> IF n = tokenPosition THEN <<"active">> ELSE @"inactive">>])
  /\ (nodeColors = nodeColors') \/ (nodeColors' = [n \in NodeSet |-> IF n = tokenPosition THEN tokenColor ELSE @"otherColor">>])
  /\ (tokenPosition = tokenPosition') \/ (tokenPosition' \in NodeSet)
  /\ (tokenColor = tokenColor') \/ (tokenColor' \in ColorDomain)

Spec ==
  Init /\ [][Next]_vars

THEOREM Spec => []Init
```