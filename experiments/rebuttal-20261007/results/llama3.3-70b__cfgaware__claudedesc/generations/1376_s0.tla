---------------------------- MODULE GrowingSet --------------------------------
EXTENDS Integers

CONSTANT Data

VARIABLE state

Data == {"d1", "d2"}

Init ==
  state = {}

Next ==
  \E x \in Data :
    state' = state \cup {x}

Spec ==
  Init /\ [][Next]_state

=============================================================================