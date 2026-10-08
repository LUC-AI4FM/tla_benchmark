```
MODULE SimpleStateMachine
EXTENDS Integers, FiniteSets

CONSTANTS NodeSet, ColorSet
ASSUME NodeSet \subseteq {1, 2, 3}
ASSUME ColorSet = {"Red", "Green"}

VARIABLES nodeActivityStatus, nodeColors, tokenPosition, tokenColor

Init ==
  /\ nodeActivityStatus \in [NodeSet -> {0, 1}]
  /\ nodeColors \in [NodeSet -> ColorSet]
  /\ tokenPosition \in NodeSet
  /\ tokenColor \in ColorSet
  /\ \A n \in NodeSet : nodeActivityStatus[n] = 1 => nodeColors[n] = "Red"

Next ==
  /\ (tokenPosition' \in NodeSet)
  /\ (tokenColor' \in ColorSet)
  /\ \UNCHANGED nodeActivityStatus
  /\ \UNCHANGED nodeColors
  /\ tokenPosition' /= tokenPosition

Spec == Init /\ [][Next]_vars

THEOREM Spec => []Init
```