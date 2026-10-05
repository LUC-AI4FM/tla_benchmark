------------------------------- MODULE Consensus -------------------------------
EXTENDS FiniteSets

CONSTANTS Values

VARIABLES chosen

vars == <<chosen>>

TypeOK == /\ chosen \subseteq Values
          /\ IsFiniteSet(chosen)

ConsistencyInv == Cardinality(chosen) <= 1

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ WF_vars(Next)

Success == <>(chosen # {})

THEOREM Spec => []TypeOK

THEOREM Spec => []ConsistencyInv

THEOREM LiveSpec => Success

================================================================================