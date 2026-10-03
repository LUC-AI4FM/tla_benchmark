---------------------------- MODULE SimpleStateMachine ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS NodeSet, ColorSet
VARIABLES nodeActivity, nodeColors, tokenPosition, tokenColor

Init ==
  /\ nodeActivity \in [NodeSet -> {<<"active">>, <<"inactive">>}]
  /\ nodeColors \in [NodeSet -> ColorSet]
  /\ tokenPosition \in NodeSet
  /\ tokenColor \in ColorSet
  /\ DOMAIN nodeActivity = NodeSet
  /\ DOMAIN nodeColors = NodeSet

Next ==
  /\ nodeActivity' \in [NodeSet -> {<<"active">>, <<"inactive">>}]
  /\ nodeColors' \in [NodeSet -> ColorSet]
  /\ tokenPosition' \in NodeSet
  /\ tokenColor' \in ColorSet
  /\ DOMAIN nodeActivity' = NodeSet
  /\ DOMAIN nodeColors' = NodeSet
  /\ (tokenPosition' = tokenPosition) \/ (tokenPosition' \in NodeSet)
  /\ (tokenColor' = tokenColor) \/ (tokenColor' \in ColorSet)

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Init
=============================================================================