```
MODULE GrowingSet
EXTENDS Integers

CONSTANTS Data

VARIABLES state

Init == state = {}

Next == state' = state \cup {x \in Data}

Spec == Init /\ [][Next]_state

THEOREM Spec => [](state \subseteq Data)
```