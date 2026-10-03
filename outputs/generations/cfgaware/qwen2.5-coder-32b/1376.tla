------------------------------- MODULE SmallStateTransition ------------------------------

CONSTANTS Data

VARIABLES state

Init == state = {}

Next ==
    /\ \/ \E x \in Data : state' = state \cup {x}
       \/ state' = state

=============================================================================