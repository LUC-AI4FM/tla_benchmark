--------------------------- MODULE SimpleStateMachine ---------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    NODE,      \* Finite, nonempty set of nodes
    COLOR      \* Domain of exactly two colors

ASSUME
  /\ NODE /= {}
  /\ IsFiniteSet(NODE)
  /\ IsFiniteSet(COLOR)
  /\ Cardinality(COLOR) = 2

VARIABLES
  active,      \* Node activity status: NODE -> BOOLEAN
  nodeColor,   \* Node colors: NODE -> COLOR
  tokenPos,    \* Token position: an element of NODE
  tokenColor   \* Token color: an element of COLOR

vars == << active, nodeColor, tokenPos, tokenColor >>

TypeOK ==
  /\ active \in [NODE -> BOOLEAN]
  /\ nodeColor \in [NODE -> COLOR]
  /\ tokenPos \in NODE
  /\ tokenColor \in COLOR

Init ==
  /\ TypeOK
  /\ tokenColor = nodeColor[tokenPos]
  /\ \E n \in NODE: active[n] = TRUE

Next ==
  /\ active' \in [NODE -> BOOLEAN]
  /\ nodeColor' \in [NODE -> COLOR]
  /\ tokenPos' \in NODE
  /\ tokenColor' \in COLOR
  /\ tokenColor' = nodeColor'[tokenPos']
  /\ \E n \in NODE: active'[n] = TRUE

Spec ==
  Init /\ [][Next]_vars

=============================================================================