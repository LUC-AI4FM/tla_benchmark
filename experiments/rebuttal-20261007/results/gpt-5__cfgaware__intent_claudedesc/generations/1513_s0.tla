------------------------------ MODULE DSTerminationStub ------------------------------

(*
  Minimal stub for a Dijkstra–Scholten token-based termination detection system
  over a small, fixed set of nodes. Both initialization and transitions are
  intentionally unconstrained with respect to node activity, node colors, and
  token position. The token color is fixed to Black throughout.
*)

CONSTANTS

(*
  Fixed, small node set and color set.
*)
Nodes == {0, 1, 2}
White == "white"
Black == "black"
Colors == {White, Black}

VARIABLES
  nodeActive,   \* [Nodes -> BOOLEAN]
  nodeColor,    \* [Nodes -> Colors]
  tokenPos,     \* element of Nodes
  tokenColor    \* element of Colors, fixed to Black throughout

vars == << nodeActive, nodeColor, tokenPos, tokenColor >>

(*
  Type invariant: node activity is a boolean assignment over Nodes,
  node colors are in Colors, token position is a valid node, and
  token color is in Colors.
*)
TypeInv ==
  /\ nodeActive \in [Nodes -> BOOLEAN]
  /\ nodeColor \in [Nodes -> Colors]
  /\ tokenPos \in Nodes
  /\ tokenColor \in Colors

(*
  Unconstrained initialization within the type constraints,
  with tokenColor fixed to Black.
*)
Init ==
  /\ nodeActive \in [Nodes -> BOOLEAN]
  /\ nodeColor \in [Nodes -> Colors]
  /\ tokenPos \in Nodes
  /\ tokenColor = Black

(*
  Unconstrained transition: any reassignment within type constraints,
  with tokenColor fixed to Black in the next state.
*)
Next ==
  /\ nodeActive' \in [Nodes -> BOOLEAN]
  /\ nodeColor' \in [Nodes -> Colors]
  /\ tokenPos' \in Nodes
  /\ tokenColor' = Black

Spec == Init /\ [][Next]_vars

=============================================================================