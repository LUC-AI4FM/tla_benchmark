------------------------------ MODULE Consensus ------------------------------

EXTENDS FiniteSets

CONSTANT Values

VARIABLES chosen

vars == << chosen >>

Init == chosen = {}

Next ==
  /\ chosen = {}
  /\ \E v \in Values: chosen' = {v}

TypeOK ==
  /\ chosen \subseteq Values
  /\ IsFiniteSet(chosen)

ConsistencyInv == Cardinality(chosen) <= 1

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ WF_vars(Next)

Success == <> (chosen # {})

THEOREM Spec => []TypeOK

THEOREM Spec => []ConsistencyInv

THEOREM LiveSpec => Success

=============================================================================