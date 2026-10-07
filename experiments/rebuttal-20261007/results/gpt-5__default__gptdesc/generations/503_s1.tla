----------------------------- MODULE SingleValueConsensus -----------------------------

EXTENDS TLC

CONSTANT Values

ASSUME Values # {}

VARIABLES chosen

vars == << chosen >>

Init ==
  chosen = {}

Next ==
  /\ chosen = {}
  /\ \E v \in Values : chosen' = {v}

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  (chosen = {}) \/ (\E v \in Values : chosen = {v})

AtMostOneChosen ==
  \A x \in chosen : \A y \in chosen : x = y

THEOREM TypeIsInvariant ==
  Spec => []TypeOK
PROOF OMITTED

THEOREM Safety_AtMostOneChosen ==
  Spec => []AtMostOneChosen
PROOF OMITTED

SpecFair ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

EventuallyChosen ==
  <>(chosen # {})

THEOREM Liveness_EventuallyChosen ==
  SpecFair => EventuallyChosen
PROOF OMITTED

=============================================================================