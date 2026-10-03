--------------------------- MODULE SingleValueConsensus ---------------------------

EXTENDS Naturals

CONSTANTS Values

NonEmptyValues == Values # {}
ASSUME NonEmptyValues

VARIABLES chosen

Init ==
  chosen = {}

Choose(v) ==
  /\ chosen = {}
  /\ v \in Values
  /\ chosen' = {v}

Next ==
  \E v \in Values: Choose(v)

Spec ==
  Init /\ [][Next]_chosen

UniqueChoice ==
  chosen = {} \/ (\E v \in Values: chosen = {v})

THEOREM Spec => []UniqueChoice

LiveSpec ==
  Spec /\ WF_chosen(Next)

THEOREM LiveSpec => <> (\E v \in Values: chosen = {v})

=============================================================================