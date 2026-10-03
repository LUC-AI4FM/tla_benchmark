------------------------------ MODULE SmallSetGrow ------------------------------

EXTENDS TLC

CONSTANTS Data

VARIABLES state

Init ==
    state = {}

Next ==
    ∃ d ∈ Data : state' = state ∪ {d}

Spec ==
    Init /\ [] [Next]_state

============================================================