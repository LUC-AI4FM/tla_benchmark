```
MODULE StateTransitionSystem
EXTENDS Integers

CONSTANTS Data

VARIABLES state

Init == state = {}

Next == 
  \E x \in Data : 
    state' = state \cup {x}

Spec == Init /\ [][Next]_

THEOREM Spec => []state \subseteq Data
```
Note: The `THEOREM` statement was added to include a safety invariant, as the original description did not provide any. This theorem states that the `state` variable is always a subset of `Data`.