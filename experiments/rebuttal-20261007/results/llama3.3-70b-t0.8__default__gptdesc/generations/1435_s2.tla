```
MODULE OneVariableSystem
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == (x = 0)

Next == (x' = x)

Spec == Init /\ [][Next]_x

THEOREM Spec => [](x = 0)
```