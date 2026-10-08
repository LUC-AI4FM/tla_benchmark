---------------------------- MODULE SmallSystem ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Data

VARIABLES state

Init == state = {}

Next ==
  /\ \/ \E d \in Data : state' = state \cup {d}
     \/ state' = state

Spec == Init /\ [][Next]_<<state>>

=============================================================================