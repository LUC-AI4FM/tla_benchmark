---- MODULE MonotonicSet ----

VARIABLES state

Data == {"d1", "d2"}

Init == state = {}

Next == ∃ d \in Data \ state : state' = state \cup {d}

Spec == Init /\ [][Next]_state

====