------------------------------ MODULE Consensus ------------------------------
EXTENDS Naturals, SETS, Temporal
CONSTANTS Values
VARIABLE chosen

Init ==
  chosen = {}

Next ==
  /\ chosen = {}
  /\ CHOOSE v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_chosen

Invariant == (chosen = {}) \/ (#(chosen) = 1)

THEOREM Safety
  []Invariant

LiveSpec == Init /\ [][Next]_chosen /\ WF_0(Next)
=============================================================================