------------------------------ MODULE Consensus ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Values

VARIABLE chosen

TypeOK == /\ chosen \subseteq Values
          /\ IsFiniteSet(chosen)

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_chosen

ConsistencyInv == Cardinality(chosen) \leq 1

Inv == TypeOK /\ ConsistencyInv

THEOREM Invariance == Spec => []Inv

-----------------------------------------------------------------------------

LiveSpec == Spec /\ WF_chosen(Next)

Success == <>(chosen # {})

ASSUME ValuesNonempty == Values # {}

THEOREM LivenessTheorem == LiveSpec => Success
=============================================================================