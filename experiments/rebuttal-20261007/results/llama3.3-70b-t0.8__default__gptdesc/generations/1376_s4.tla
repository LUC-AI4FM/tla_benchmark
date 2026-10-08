```
MODULE SmallStateTransitionSystem
EXTENDS Integers

CONSTANTS Data

VARIABLES state

Init == state = {}

Next == 
  \E x \in Data : 
    state' = state \cup {x}

Spec == Init /\ [][Next]_
```