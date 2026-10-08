MODULE MultiSlotConsensus

EXTENDS Naturals, FiniteSets

CONSTANTS Slots, Values

VARIABLES proposed, chosen

(* ------------------------------------------------------------------ *)
(* Actions *)

ProposeAction(v) == 
  /\ v ∈ Values \ proposed
  /\ proposed' = proposed ∪ {v}
  /\ chosen'   = chosen

ChooseAction(s, v) ==
  /\ s ∈ Slots
  /\ chosen[s] = {}
  /\ v ∈ proposed
  /\ chosen'   = [chosen EXCEPT ![s] = {v}]
  /\ proposed' = proposed

Next == 
  ∃v ∈ Values \ proposed : ProposeAction(v)
  \/ ∃s ∈ Slots, v ∈ proposed : ChooseAction(s,v)

(* ------------------------------------------------------------------ *)
(* Initial state *)

Init ==
  /\ proposed = {}
  /\ chosen   = [s ∈ Slots |-> {}]

(* ------------------------------------------------------------------ *)
(* Invariants *)

TypeOK == 
  /\ proposed ⊆ Values
  /\ ∀s ∈ Slots : chosen[s] ⊆ Values
  /\ ∀s ∈ Slots : Cardinality(chosen[s]) ≤ 1

NontrivialProposals ==
  ∃v ∈ proposed

NontrivialChoices ==
  ∃s ∈ Slots : chosen[s] ≠ {}

Stability == 
  ∀s ∈ Slots : (chosen[s] ≠ {} ⇒ chosen' [s] = chosen[s])

PerSlotConsistency ==
  ∀s ∈ Slots : chosen[s] ⊆ proposed

(* ------------------------------------------------------------------ *)
(* Liveness property *)

Liveness ==
  ∀s ∈ Slots : <> (chosen[s] ≠ {})

(* ------------------------------------------------------------------ *)
(* Specification *)

Spec == Init /\ [][Next]_vars /\ WF_0(Next)

Safety == 
  []TypeOK
  /\ []NontrivialProposals
  /\ []NontrivialChoices
  /\ []PerSlotConsistency
  /\ []Stability

=============================================================================