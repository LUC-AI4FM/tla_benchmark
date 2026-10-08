------------------------------- MODULE GitHub407Test -------------------------------

CONSTANTS Data

VARIABLE state

Init == state = {}

Next ==
    \/ /\ \E x \in Data : ~x \in state
       /\ state' = state \cup {x}
    \/ state' = state

Spec == Init /\ [][Next]_<<state>>

=============================================================================