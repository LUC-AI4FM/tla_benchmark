------------------------------ MODULE SmallStateSystem ------------------------------

EXTENDS TLC

CONSTANT Data

VARIABLES state

Init ==
  state = {}

Next ==
  ∃ d \in Data : state' = state \cup {d}

Spec ==
  Init /\ [][Next]_state

=============================================================================