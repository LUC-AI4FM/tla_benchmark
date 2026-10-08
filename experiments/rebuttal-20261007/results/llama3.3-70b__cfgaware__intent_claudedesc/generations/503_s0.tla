---------------------------- MODULE Consensus ----------------------------
EXTENDS Integers

CONSTANT Candidates
VARIABLE chosen

Init == (chosen = {})

ChooseValue(v) == (v \in Candidates) ∧ (chosen' = {v})

Next == (∃ v \in Candidates : ChooseValue(v)) ∨ (chosen' = chosen)

Spec == Init ∧ [][Next]_chosen

LiveSpec == Spec ∧ WF_vars(ChooseValue, <<>>)
=============================================================================