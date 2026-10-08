```
MODULE ConstantState
EXTENDS Integers

CONSTANTS None

VARIABLES state

Init == state = 0

Next == state' = state

Spec == Init /\ [][Next]_state

Invariant == state = 0

THEOREM Spec => []Invariant
THEOREM Spec => <><>True
```