```
MODULE SmallStateMachine
EXTENDS Integers
CONSTANTS Op
VARIABLES x

Init == (x = 0)

Next == x' \in Op(x)

Spec == Init /\ [][Next]_x

TypeInv == x \in Nat

subsetOp(x) == {y \in Op(x) : y > x}
isConstantOp(x) == Op(x) = {x}

THEOREM Spec => []TypeInv
```
Note: This specification assumes that `Nat` is the set of natural numbers, which includes 0. If this is not the case in your specific TLA+ environment, you might need to adjust `TypeInv` accordingly.