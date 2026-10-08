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
  /\ (tokenPosition' = tokenPosition) \/ (tokenPosition' \in NodeSet)
  /\ (tokenColor' = tokenColor) \/ (tokenColor' \in ColorDomain)

Spec ==
  Init /\ [][Next]_vars

THEOREM Spec => []Init
```
Note: I assumed `NodeSet` and `ColorDomain` are finite sets of nodes and colors respectively. Also, `nodeActivityStatus`, `nodeColors`, `tokenPosition`, and `tokenColor` are variables that take values from these sets. The `Next` relation allows the state to change in a way that respects the constraints on the variables.