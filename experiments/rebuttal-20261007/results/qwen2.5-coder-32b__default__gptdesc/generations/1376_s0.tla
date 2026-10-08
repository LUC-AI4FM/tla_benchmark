------------------------------- MODULE SmallStateTransition -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Data

VARIABLES state

Init == state = {}

Next ==
  \/ /\ CHOOSE x \in Data: TRUE
     /\ state' = state \cup {x}

Spec == Init /\ [][Next]_<<state>>
=============================================================================