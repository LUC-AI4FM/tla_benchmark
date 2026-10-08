```
MODULE SimpleStateMachine
EXTENDS Integers, FiniteSets

CONSTANTS NodeSet, ColorSet
ASSUME NodeSet \in SUBSET FiniteSet &&
       ColorSet = {"Red", "Green"}

VARIABLES nodeActivityStatus,
          nodeColors,
          tokenPosition,
          tokenColor

Init ==
  /\ nodeActivityStatus \in [NodeSet -> {<<"Active">>, <<"Inactive">>}]
  /\ nodeColors \in [NodeSet -> ColorSet]
  /\ tokenPosition \in NodeSet
  /\ tokenColor \in ColorSet
  /\ \A n \in NodeSet : nodeActivityStatus[n] = <<"Active">> => nodeColors[n] = "Green"

Next ==
  /\ nodeActivityStatus' \in [NodeSet -> {<<"Active">>, <<"Inactive">>}]
  /\ nodeColors' \in [NodeSet -> ColorSet]
  /\ tokenPosition' \in NodeSet
  /\ tokenColor' \in ColorSet
  /\ \A n \in NodeSet : nodeActivityStatus'[n] = <<"Active">> => nodeColors'[n] = "Green"
  /\ (tokenPosition' = tokenPosition) \/ (tokenPosition' \in NodeSet)
  /\ (tokenColor' = tokenColor) \/ (tokenColor' \in ColorSet)

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Init
```