------------------------------ MODULE Consensus ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANT Values

VARIABLES chosen

vars == << chosen >>

Init ==
  chosen = {}

Next ==
  /\ chosen = {}
  /\ \E v \in Values: chosen' = {v}

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  /\ chosen \subseteq Values
  /\ IsFiniteSet(chosen)

ConsistencyInv ==
  Cardinality(chosen) <= 1

LiveSpec ==
  Spec /\ WF_vars(Next)

Success ==
  <> (chosen /= {})

THEOREM Spec => []TypeOK

THEOREM Spec => []ConsistencyInv

THEOREM LiveSpec => Success

=============================================================================