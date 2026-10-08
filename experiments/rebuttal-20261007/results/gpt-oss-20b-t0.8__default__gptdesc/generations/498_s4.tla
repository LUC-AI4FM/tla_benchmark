MODULE MultiSlotConsensus

EXTENDS Naturals, Sequences, TLC

CONSTANTS Slots, Values

VARIABLE Proposed, Chosen

(* --- INITIAL STATE ----------------------------------------------------- *)
Init ==
  /\ Proposed = {}
  /\ Chosen \in [Slots -> SUBSET VALUES]
  /\ ∀ s ∈ Slots : Chosen[s] = {}

(* --- ACTIONS ---------------------------------------------------------- *)

Propose ==
  /\ ∃ v ∈ Values :
        /\ v ∉ Proposed
        /\ Proposed' = Proposed ∪ {v}
        /\ Chosen' = Chosen

Choose ==
  /\ ∃ s ∈ Slots, v ∈ Proposed :
        /\ Chosen[s] = {}
        /\ Chosen' = [Chosen EXCEPT ![s] = {v}]
        /\ Proposed' = Proposed

Next == Propose \/ Choose

(* --- TYPE AND INVARIANTS ---------------------------------------------- *)

TypeOK ==
  /\ Proposed \subseteq Values
  /\ Chosen \in [Slots -> SUBSET VALUES]
  /\ ∀ s ∈ Slots : (Chosen[s] = {} \/ #Chosen[s] = 1)

PerSlotConsistency ==
  ∀ s ∈ Slots :
        Chosen[s] ≠ {} => Chosen[s] ⊆ Proposed

SafetyInvariants == TypeOK /\ PerSlotConsistency

(* --- SPECIFICATION ---------------------------------------------------- *)

Spec ==
  Init
  /\ [][Next]_<<Proposed,Chosen>>
  /\ WF_vars(Next)
  /\ SafetyInvariants

(* --- LIVENESS PROPERTIES ---------------------------------------------- *)

THEOREM Spec => []<>(∀ s ∈ Slots : Chosen[s] ≠ {})
