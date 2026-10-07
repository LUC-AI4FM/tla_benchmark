------------------------------ MODULE SimpleStateMachine ------------------------------

EXTENDS TLC

(*
  A simple state machine with:
  - active: mapping from nodes to boolean activity status
  - nodeColor: mapping from nodes to colors
  - tokenPos: the node currently holding the token
  - tokenColor: the color of the token

  The small, fixed universe:
    - NODES: three nodes
    - COLORS: two colors
*)

NODES == {"n1", "n2", "n3"}
COLORS == {"red", "blue"}

VARIABLES active, nodeColor, tokenPos, tokenColor

TypeOK ==
  /\ active \in [NODES -> BOOLEAN]
  /\ nodeColor \in [NODES -> COLORS]
  /\ tokenPos \in NODES
  /\ tokenColor \in COLORS

(*
  Additional state constraint:
  The token's color always equals the color of the node where the token resides.
*)
TokenMatches ==
  tokenColor = nodeColor[tokenPos]

Init ==
  /\ TypeOK
  /\ TokenMatches

Next ==
  /\ TypeOK'
  /\ tokenColor' = nodeColor'[tokenPos']

vars == << active, nodeColor, tokenPos, tokenColor >>

Spec ==
  Init /\ [][Next]_vars

=============================================================================