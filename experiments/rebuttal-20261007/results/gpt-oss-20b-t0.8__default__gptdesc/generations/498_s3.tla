------------------------------ MODULE MultiSlotConsensus ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Slots, Values  \* finite non‑empty sets of slot identifiers and values

VARIABLES Proposed, Chosen

(* --------------------------------------------------------------------------- *)
(* Initial state: no proposals, all slots empty.                               *)
Init ==
    /\ Proposed = ∅
    /\ Chosen   = [ s \in Slots |-> ∅ ]

(* --------------------------------------------------------------------------- *)
(* Action to add a new proposal.                                               *)
AddPropose(v) ==
    /\ v ∈ Values
    /\ v ∉ Proposed
    /\ Proposed' = Proposed ∪ {v}
    /\ Chosen'   = Chosen

(* --------------------------------------------------------------------------- *)
(* Action to choose a proposed value for an empty slot.                        *)
ChooseSlot(s, v) ==
    /\ s ∈ Slots
    /\ Chosen[s] = ∅
    /\ v ∈ Proposed
    /\ Chosen'   = [Chosen EXCEPT ![s] = {v}]
    /\ Proposed' = Proposed

(* --------------------------------------------------------------------------- *)
(* Next action: either add a proposal or choose a slot.                        *)
Next ==
    \E v \in Values : AddPropose(v)
    \/ \E s \in Slots, v \in Proposed : ChooseSlot(s,v)

(* --------------------------------------------------------------------------- *)
(* Safety invariants.                                                         *)

(* Type correctness: Proposed ⊆ Values and each Chosen[s] is empty or a singleton from Proposed. *)
TypeCorrectness ==
    /\ Proposed ⊆ Values
    /\ Chosen ∈ [ Slots -> SUBSET Values ]
    /\ \A s \in Slots :
        Chosen[s] = ∅ \/ (∃ v ∈ Proposed : Chosen[s] = {v})

(* Non‑triviality: either there is at least one proposal or all slots are empty. *)
Nontriviality ==
    Proposed ≠ ∅ \/ (\A s \in Slots : Chosen[s] = ∅)

Safety == TypeCorrectness /\ Nontriviality

THEOREM SafeInvariant == [] Safety

(* --------------------------------------------------------------------------- *)
(* Liveness property: under weak fairness of Next, eventually every slot becomes nonempty. *)

AllSlotsChosen ==
    \A s \in Slots : Chosen[s] ≠ ∅

Liveness ==
    WF(Next) => <> AllSlotsChosen

THEOREM LivenessProperty == Liveness

(* --------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<Proposed, Chosen>> /\ WF(Next)

=============================================================================