```
MODULE SmallStateMachine
EXTENDS Integers
CONSTANTS Op
VARIABLES x

Init == (x = 0)

Next == (x' \in Op(x))

Spec == Init /\ [][Next]_x

TypeInvariant == x \in Nat

SafetyInv == TypeInvariant

THEOREM Spec => []SafetyInv
```