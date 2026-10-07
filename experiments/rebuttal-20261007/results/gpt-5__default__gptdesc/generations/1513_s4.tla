--------------------------- MODULE SimpleStateMachine ---------------------------

EXTENDS Naturals

CONSTANTS Node, ColorDom

ASSUME Node = {1, 2, 3}
ASSUME ColorDom = {"red", "blue"}

VARIABLES Active, NodeColors, TokenPos, TokenColor

vars == << Active, NodeColors, TokenPos, TokenColor >>

TypeOK ==
  /\ Active \subseteq Node
  /\ NodeColors \in [Node -> ColorDom]
  /\ TokenPos \in Node
  /\ TokenColor \in ColorDom
  /\ TokenColor = NodeColors[TokenPos]

Init ==
  TypeOK

Toggle(n) ==
  /\ Active' = IF n \in Active THEN Active \ {n} ELSE Active \cup {n}
  /\ NodeColors' = NodeColors
  /\ TokenPos' = TokenPos
  /\ TokenColor' = NodeColors'[TokenPos']

Recolor(n) ==
  \E c \in ColorDom:
    /\ NodeColors' = [NodeColors EXCEPT ![n] = c]
    /\ Active' = Active
    /\ TokenPos' = TokenPos
    /\ TokenColor' = NodeColors'[TokenPos']

Move(n) ==
  /\ TokenPos' = n
  /\ Active' = Active
  /\ NodeColors' = NodeColors
  /\ TokenColor' = NodeColors'[TokenPos']

Next ==
  \E n \in Node:
    /\ (Toggle(n) \/ Recolor(n) \/ Move(n))
    /\ TypeOK'

Spec ==
  Init /\ [][Next]_vars

=============================================================================