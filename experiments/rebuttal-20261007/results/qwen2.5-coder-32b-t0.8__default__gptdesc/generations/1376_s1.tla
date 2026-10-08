```tla
MODULE SmallStateSystem

EXTENDS TLC

CONSTANTS Data

VARIABLES state

Init == state = {}

Next == /\ \/  \E x \in Data : state' = state \cup {x}
         /\ state' \subseteq Data

Spec == Init /\ [][Next]_<<state>>
```