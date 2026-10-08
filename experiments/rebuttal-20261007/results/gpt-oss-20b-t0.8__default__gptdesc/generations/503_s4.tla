MODULE SingleConsensus
EXTENDS Naturals

CONSTANTS Values

VARIABLE chosen

Init ==
  chosen = {}

Choose ==
  (chosen = {} /\ ∃ v ∈ Values : chosen' = {v})

Stutter ==
  chosen' = chosen

Next ==
  Choose \/ Stutter

Spec ==
  Init /\ [][Next]_chosen

Inv ==
  (chosen = {}) \/ (∃ v ∈ Values : chosen = {v})

THEOREM Safety == Spec => []Inv

SpecWF ==
  Init /\ WF_vars(Choose) /\ [][Next]_chosen

THEOREM Liveness == SpecWF => <> (∃ v ∈ Values : chosen = {v})