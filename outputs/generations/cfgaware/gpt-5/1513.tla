--------------------------- MODULE SimpleStateMachine ---------------------------

CONSTANTS NODES, COLORS

VARIABLES active, colors, token, tokColor

vars == << active, colors, token, tokColor >>

TypeOK ==
  /\ active \subseteq NODES
  /\ colors \in [NODES -> COLORS]
  /\ token \in NODES
  /\ tokColor \in COLORS

Init ==
  /\ TypeOK
  /\ token \in active
  /\ tokColor = colors[token]

Next ==
  \E a \subseteq NODES:
    \E c \in [NODES -> COLORS]:
      \E t \in NODES:
        \E tc \in COLORS:
          /\ active' = a
          /\ colors' = c
          /\ token' = t
          /\ tokColor' = tc
          /\ t \in a
          /\ tc = c[t]

Spec ==
  Init /\ [][Next]_vars

=============================================================================