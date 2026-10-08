```
MODULE PositivityConstraint
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == (x = 23)

Next == (* nondeterministically assign 0 or 1, but only if positive *)
        /\ x' \in {0, 1}
        /\ x' > 0

Spec == Init /\ [][Next]_x

THEOREM Spec => []<>(x /= 0)
```