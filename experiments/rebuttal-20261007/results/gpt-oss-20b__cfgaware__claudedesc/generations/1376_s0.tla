------------------------------ MODULE MonotonicSet ------------------------------
CONSTANTS Data = {"d1", "d2"}

VARIABLE state

Init == state = {}

Next == \E x \in Data : state' = state \cup {x}

Spec == Init /\ [][Next]_state
=============================================================================