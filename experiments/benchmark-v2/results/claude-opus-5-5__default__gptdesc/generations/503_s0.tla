------------------------------ MODULE Consensus ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT Values

ASSUME ValuesNonEmpty == Values # {}

VARIABLE chosen

vars == <<chosen>>

TypeOK == /\ chosen \subseteq Values
          /\ IsFiniteSet(chosen)

Init == chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_chosen

-----------------------------------------------------------------------------
(* Safety: at most one value is ever chosen.                               *)
-----------------------------------------------------------------------------

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv

-----------------------------------------------------------------------------
(* Liveness: with weak fairness on Next, some value is eventually chosen.  *)
-----------------------------------------------------------------------------

LiveSpec == Spec /\ WF_chosen(Next)

Success == <>(chosen # {})

THEOREM LivenessTheorem == LiveSpec => Success

=============================================================================