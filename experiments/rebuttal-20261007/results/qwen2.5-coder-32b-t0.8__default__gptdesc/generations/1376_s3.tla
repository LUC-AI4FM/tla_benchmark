------------------------------ MODULE SmallStateSystem ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Data

VARIABLES state

Init == state = {}

Next ==
    \/ /\ CHOOSE e \in Data: TRUE
       /\ state' = state \cup {e}

Spec == Init /\ [][Next]_<<state>>
=============================================================================