---------------------------- MODULE Consensus ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Values

VARIABLE chosen

vars == <<chosen>>

TypeOK == /\ chosen \subseteq Values
          /\ IsFiniteSet(chosen)

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_vars

ConsistencyInv == /\ TypeOK
                  /\ Cardinality(chosen) \leq 1

LiveSpec == Spec /\ WF_vars(Next)

Success == <>(chosen # {})

THEOREM Invariance == Spec => []ConsistencyInv

THEOREM LivenessTheorem == LiveSpec => Success
=============================================================================