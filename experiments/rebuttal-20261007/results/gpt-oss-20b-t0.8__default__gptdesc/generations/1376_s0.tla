------------------------------ MODULE StateTransition ------------------------------
CONSTANTS Data
VARIABLE state

Init ==  state = {}

Next == \E x \in Data : state' = state \cup {x}

Spec == Init /\ [][Next]_state
=============================================================================