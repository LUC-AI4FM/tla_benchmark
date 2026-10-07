------------------------------- MODULE GitHub407Test -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS Data

VARIABLES state

Init == state = {}

Next ==
  \/ /\ state \in SUBSET Data
     /\ CHOOSE x \in Data \ state : state' = state \cup {x}
  \/ /\ state = Data
     /\ state' = state

Spec == Init /\ [][Next]_<<state>>

=============================================================================