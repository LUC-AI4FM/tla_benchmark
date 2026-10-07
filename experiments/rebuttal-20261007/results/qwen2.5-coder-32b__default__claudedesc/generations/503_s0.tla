------------------------------- MODULE Consensus -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Values

VARIABLES chosen

Init == chosen = {}

Next ==
  /\ chosen = {}
  /\ \/ \E v \in Values : chosen' = {v}
     \/ chosen' = chosen

TypeOK == chosen \subseteq Values /\ Finite(chosen)

ConsistencyInv == Cardinality(chosen) <= 1

Spec == Init /\ [][Next]_<<chosen>>

LiveSpec == Spec /\ WF_next(Next)

Success == <>(Cardinality(chosen) > 0)

THEOREM Spec => []TypeOK
THEOREM Spec => [](TypeOK /\ ConsistencyInv)
THEOREM LiveSpec => Success

=============================================================================