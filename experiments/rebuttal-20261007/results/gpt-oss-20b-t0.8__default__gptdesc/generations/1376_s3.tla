```
MODULE DataUnion
EXTENDS TLC

CONSTANTS Data

VARIABLE state

Init == state = {}

Next ==
  ∃ e \in Data :
    state' = state ∪ {e}

Spec == Init /\ []Next
```