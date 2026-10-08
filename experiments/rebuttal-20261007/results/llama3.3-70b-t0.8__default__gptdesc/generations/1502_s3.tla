```
MODULE SmallStateMachine
EXTENDS Integers
CONSTANTS Op
VARIABLES x

Init == (x = 0)

Next == (x' \in Op(x))

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
```