------------------------------ MODULE Consensus ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Values

ASSUME ValuesNonEmpty == Values # {}

VARIABLE chosen

vars == <<chosen>>

-----------------------------------------------------------------------------
TypeOK == /\ chosen \subseteq Values
          /\ IsFiniteSet(chosen)

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_chosen

-----------------------------------------------------------------------------
(* Safety: at most one value is ever chosen. *)
Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv

-----------------------------------------------------------------------------
(* Liveness: with weak fairness on Next, eventually some value is chosen. *)
Success == <>(chosen # {})

LiveSpec == Spec /\ WF_chosen(Next)

THEOREM LivenessTheorem == LiveSpec => Success

=============================================================================