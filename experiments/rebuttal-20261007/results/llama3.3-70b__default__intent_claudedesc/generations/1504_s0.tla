```
MODULE StationarySystem
EXTENDS Integers

CONSTANTS 

VARIABLES state

Init == state = TRUE

Next == state' = state

Spec == Init /\ [][Next]_state

THEOREM Spec => []<><>Next
```