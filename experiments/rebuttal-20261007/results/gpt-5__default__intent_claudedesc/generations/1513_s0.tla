------------------------------ MODULE DS_Token_Stub ------------------------------

EXTENDS TLC

CONSTANTS NODES

ASSUME NODES = {0, 1, 2}

VARIABLES
  active,      \* [NODES -> BOOLEAN]
  color,       \* [NODES -> Colors]
  tokenPos,    \* element of NODES
  tokenColor   \* element of Colors, fixed to Black

Colors == {"white", "black"}
Black  == "black"

TypeInv ==
  /\ active \in [NODES -> BOOLEAN]
  /\ color \in [NODES -> Colors]
  /\ tokenPos \in NODES
  /\ tokenColor \in Colors

TokenBlackInv == tokenColor = Black

vars == << active, color, tokenPos, tokenColor >>

Init ==
  /\ active \in [NODES -> BOOLEAN]
  /\ color \in [NODES -> Colors]
  /\ tokenPos \in NODES
  /\ tokenColor = Black

Next ==
  /\ active' \in [NODES -> BOOLEAN]
  /\ color' \in [NODES -> Colors]
  /\ tokenPos' \in NODES
  /\ tokenColor' = Black

Spec == Init /\ [][Next]_vars

=============================================================================