MODULE SmallStateSystem
EXTENDS Naturals

CONSTANT Data

VARIABLE state

Init == state = {}

Next == ∃ e \in Data : state' = state ∪ {e}

Spec == Init /\ [][Next]_state