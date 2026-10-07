MODULE MonotonicSet
EXTENDS TLC

CONSTANTS Data

Data == {"d1", "d2"}

VARIABLE state

Init == state = {}

Next == ∃ x ∈ Data : state' = state ∪ {x}

Spec == Init /\ [][Next]_state