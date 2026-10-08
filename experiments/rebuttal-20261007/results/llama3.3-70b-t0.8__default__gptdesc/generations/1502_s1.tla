```
MODULE SmallStateMachine
EXTENDS Integers
CONSTANTS Op
VARIABLES x

Init == (x = 0)

Next == (x' \in Op(x))

Spec == Init /\ [][Next]_x

HelperOp1(x) == {y \in Op(x) : y > x}

HelperOp2(x) == {y \in Op(x) : y < x}
```