------------------------------ MODULE MultiConsensus ------------------------------
EXTENDS Naturals, TLC

CONSTANTS Values, Slots

VARIABLE proposed, chosen

vars == <<proposed, chosen>>

Init ==
  /\ proposed = {}
  /\ chosen = [s \in Slots |-> {}]

Propose ==
  ∃ v ∈ (Values \ proposed) :
    /\ proposed' = proposed ∪ {v}
    /\ chosen'   = chosen

Choose ==
  ∃ s ∈ Slots : chosen[s] = {} ∧
  ∃ v ∈ proposed :
    /\ chosen'   = [chosen EXCEPT ![s] = {v}]
    /\ proposed' = proposed

Next == Propose \/ Choose

Spec == Init /\ [] (Next)

LiveSpec == Spec /\ WF_∃(Next)

TypeOK ==
  /\ proposed ⊆ Values
  /\ chosen ∈ [Slots -> SUBSET Values]

Nontriviality ==
  ∀ s ∈ Slots : chosen[s] ⊆ proposed

Stability ==
  ∀ s ∈ Slots :
    [] ((chosen[s] ≠ {}) => [](chosen[s] ≠ {}))

Consistency ==
  ∀ s ∈ Slots : |chosen[s]| <= 1

Liveness ==
  ∀ s ∈ Slots : <> (chosen[s] ≠ {})

=============================================================================