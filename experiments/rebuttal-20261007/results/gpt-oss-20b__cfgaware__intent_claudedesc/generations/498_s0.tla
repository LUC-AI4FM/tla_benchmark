MODULE LiveSpec

CONSTANTS
  Values,
  Slots

ASSUME
  Values /= {} /\ Slots /= {}

VARIABLES
  proposals,
  chosen

TypeInvariant ==
  proposals ∈ [Slots -> SUBSET Values] /\
  chosen   ∈ [Slots -> Values \cup {FALSE}] /\
  (∀ s ∈ Slots : chosen[s] = FALSE \/ chosen[s] ∈ Values)

Init == 
  proposals = [s \in Slots |-> {}] /\ 
  chosen   = [s \in Slots |-> FALSE]

Propose ==
  ∃ s ∈ Slots, v ∈ Values :
    /\ proposals' = [proposals EXCEPT ![s] = @ ∪ {v}]
    /\ chosen'    = chosen

Choose ==
  ∃ s ∈ Slots, v ∈ Values :
    /\ chosen[s]   = FALSE
    /\ v ∈ proposals[s]
    /\ proposals' = proposals
    /\ chosen'    = [chosen EXCEPT ![s] = v]

Next == Propose \/ Choose

Nontriviality ==
  [] (∀ s ∈ Slots : chosen[s] = FALSE \/ chosen[s] ∈ proposals[s])

Stability ==
  [] (Next => ∀ s ∈ Slots : chosen[s] ≠ FALSE ⇒ chosen'[s] = chosen[s])

Consistency ==
  [] (Next => ∀ s ∈ Slots : chosen[s] = FALSE \/ chosen[s] ∈ Values)

Liveness ==
  []<> (∀ s ∈ Slots : chosen[s] ≠ FALSE)

Spec == Init /\ [][Next]_<<proposals, chosen>>

=============================================================================