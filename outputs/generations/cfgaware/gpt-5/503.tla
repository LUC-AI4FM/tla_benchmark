------------------------------ MODULE SingleValueConsensus ------------------------------

CONSTANT Values

VARIABLES chosen

vars == << chosen >>

Init ==
  chosen = {}

Next ==
  /\ chosen = {}
  /\ ∃ v \in Values: chosen' = {v}

Spec ==
  Init /\ [][Next]_vars

Singletons(S) == { {x} : x \in S }

AtMostOneChosen ==
  chosen \in ({ {} } \cup Singletons(Values))

THEOREM SafetyInvariant ==
  Spec => []AtMostOneChosen
PROOF OBVIOUS

LiveSpec ==
  Spec /\ WF_vars(Next)

EventuallyChosen ==
  <> (chosen # {})

THEOREM Liveness ==
  (Values # {}) => (LiveSpec => EventuallyChosen)
PROOF OBVIOUS

=============================================================================