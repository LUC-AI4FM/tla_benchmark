MODULE Consensus
EXTENDS Naturals

CONSTANTS Values

VARIABLE chosen

vars == <<chosen>>

Init == chosen = {}

Next ==
  /\ chosen = {}
  /\ \E v \in Values : chosen' = {v}

Spec == Init /\ [][Next]_vars

SpecFair == Init /\ WF_vars(Next) /\ [][Next]_vars

THEOREM SafetyInvariant == Spec => [] (chosen = {} \/ (\E v \in Values : chosen = {v}))

THEOREM Liveness == SpecFair => <> (chosen # {})