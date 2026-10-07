------------------------------ MODULE SingleValueConsensus ------------------------------

EXTENDS Naturals

CONSTANTS Values

ASSUME Values # {}

VARIABLES chosen

Init ==
  chosen = {}

Next ==
  /\ chosen = {}
  /\ \E v \in Values : chosen' = {v}

Spec ==
  Init /\ [][Next]_chosen

TypeOK ==
  chosen \in SUBSET Values

AtMostOneChosen ==
  \A v \in Values : \A w \in Values : (v \in chosen /\ w \in chosen) => v = w

THEOREM OneValueInvariant ==
  Spec => [](TypeOK /\ AtMostOneChosen)

LiveSpec ==
  Init /\ [][Next]_chosen /\ WF_chosen(Next)

EventuallyChosen ==
  <>(chosen # {})

THEOREM EventualChoice ==
  LiveSpec => EventuallyChosen

=============================================================================