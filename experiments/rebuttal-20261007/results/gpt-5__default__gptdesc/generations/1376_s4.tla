---- MODULE AccumulateSet ----

EXTENDS Naturals

CONSTANTS Data

VARIABLES state

Init ==
  state = {}

Next ==
  \E d \in Data:
    state' = state \cup {d}

Spec ==
  Init /\ [][Next]_state

====