----------------------------- MODULE SimpleStateMachine -----------------------------

EXTENDS Naturals, TLC

CONSTANTS NODES, COLORS

ASSUME NODES = {1, 2, 3} /\ COLORS = {"red", "blue"}

VARIABLES activity, colors, tokenPos, tokenColor

vars == << activity, colors, tokenPos, tokenColor >>

TypeOK ==
  /\ activity \subseteq NODES
  /\ colors \in [NODES -> COLORS]
  /\ tokenPos \in NODES
  /\ tokenColor \in COLORS

Consistency ==
  /\ tokenColor = colors[tokenPos]
  /\ tokenPos \in activity

Init ==
  /\ TypeOK
  /\ Consistency

Next ==
  /\ activity' \subseteq NODES
  /\ colors' \in [NODES -> COLORS]
  /\ tokenPos' \in NODES
  /\ tokenColor' \in COLORS
  /\ tokenColor' = colors'[tokenPos']
  /\ tokenPos' \in activity'

Inv == TypeOK /\ Consistency

Spec == Init /\ [][Next]_vars

================================================================================