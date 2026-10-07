----------------------------- MODULE MonotonicSet407 -----------------------------

EXTENDS Naturals

CONSTANTS Data
VARIABLES state

Init ==
  state = {}

Next ==
  ∃ d ∈ Data \ state : state' = state ∪ {d}

Spec ==
  Init /\ [][Next]_state

ASSUME Data = {"d1", "d2"}

=============================================================================