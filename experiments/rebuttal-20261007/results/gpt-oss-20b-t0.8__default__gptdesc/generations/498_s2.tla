MODULE MultiSlotConsensus
EXTENDS Naturals, TLC

CONSTANTS Slots, Values

VARIABLES proposed, chosen

vars == {proposed, chosen}

(* Type invariants *)
TypeInvariant ==
  /\ proposed \subseteq Values
  /\ chosen \subseteq Slots × Values
  /\ ∀ s ∈ Slots : (# { v : (s,v) ∈ chosen }) <= 1
  /\ ∀ s ∈ Slots, v ∈ Values : ((s,v) ∈ chosen => v ∈ proposed)

(* Safety invariants *)
SafetyInvariant ==
  /\ TypeInvariant
  /\ proposed ≠ {}

(* Actions *)

Propose(v) ==
  /\ v ∈ Values
  /\ v ∉ proposed
  /\ proposed' = proposed ∪ {v}
  /\ chosen' = chosen

Choose(s,v) ==
  /\ s ∈ Slots
  /\ v ∈ proposed
  /\ ¬∃ v0 ∈ Values : (s, v0) ∈ chosen
  /\ chosen' = chosen ∪ {(s,v)}
  /\ proposed' = proposed

Next ==
  ∃v ∈ Values : Propose(v)
  \/ ∃s ∈ Slots, v ∈ proposed : Choose(s,v)

Init ==
  /\ proposed = {}
  /\ chosen = {}

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars/Next

(* Liveness property: eventually every slot is chosen *)
Liveness ==
  ∀ s ∈ Slots : ◻◇ (∃ v ∈ Values : (s,v) ∈ chosen)

END MODULE