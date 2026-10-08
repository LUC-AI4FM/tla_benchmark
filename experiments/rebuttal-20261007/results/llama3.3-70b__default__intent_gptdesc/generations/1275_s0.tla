```
MODULE SimpleStateVariableSystem
EXTENDS Integers

CONSTANTS None

VARIABLES x

Init == (x = 0)

Next == (x' = x)

Spec == Init /\ [][Next]_x

Inv == x < 1

THEOREM Spec => []Inv
```