---- MODULE Consensus ----
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

-----------------------------------------------------------------------------
Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv

-----------------------------------------------------------------------------
LiveSpec == Spec /\ WF_vars(Next)

Success == <>(chosen # {})

ASSUME ValuesNonempty == Values # {}

THEOREM LivenessTheorem == LiveSpec => Success
=============================================================================