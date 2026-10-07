------------------------------ MODULE GrowSet ------------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES state

Init ==
  state = {}

Next ==
  ∃ d ∈ Data: state' = state ∪ {d}

Spec ==
  Init /\ [][Next]_state

============================================================================