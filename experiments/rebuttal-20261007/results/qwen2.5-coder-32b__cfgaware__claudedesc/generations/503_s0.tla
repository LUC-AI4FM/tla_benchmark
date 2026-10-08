------------------------------- MODULE Consensus -------------------------------

CONSTANTS Values

VARIABLES chosen

ASSUME CHOOSE Values \in SUBSET [1..2]

Init == chosen = {}

Next ==
  /\ chosen = {}
  /\ \/ \E v \in Values : chosen' = {v}

TypeOK == chosen \subseteq Values /\ Finite(chosen)

ConsistencyInv == Cardinality(chosen) <= 1

Spec == Init /\ [][Next]_<<chosen>>

LiveSpec == Spec /\ WF_next(Next, <<chosen>>)

Success == <>(chosen /= {})

THEOREM Spec => []TypeOK
THEOREM Spec => [](TypeOK /\ ConsistencyInv)
THEOREM LiveSpec => <>Success

=============================================================================