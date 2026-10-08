--------------------------- MODULE Consensus ---------------------------
EXTENDS TLC

CONSTANTS Values

VARIABLES chosen

Init == chosen = {}

Choose(v) == (chosen = {}) /\ (chosen' = {v}) /\ v ∈ Values

Next == ∃ v ∈ Values : Choose(v)

ChosenInv ==
    (chosen = {}) \/ (∃ v ∈ Values : chosen = {v})

Spec == Init /\ [][Next]_chosen

SpecFair == Init /\ [][Next]_chosen /\ WF(Next)

THEOREM Safety_Inv_Holds == Spec => [] ChosenInv

THEOREM Liveness_Choose == SpecFair => <> (chosen # {})

=============================================================================