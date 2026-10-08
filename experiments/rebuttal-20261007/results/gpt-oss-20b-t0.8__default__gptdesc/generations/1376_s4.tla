MODULE SmallState

EXTENDS TLC

CONSTANTS Data

VARIABLE state

Init == state = {}

Next == ∃ x \in Data : state' = state \cup {x}

Spec == Init /\ [][Next]_state