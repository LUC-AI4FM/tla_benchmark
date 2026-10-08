```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x

fact(n) == IF n = 0 THEN 1 ELSE n * fact(n-1)

Init == x = 0

A == x' = fact(3)
B == x' = fact(9)

Next == A \/ B

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
```