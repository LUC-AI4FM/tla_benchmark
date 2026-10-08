```
MODULE DemoInit
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == (x \in {0})

Next == FALSE

Spec == Init /\ [][Next]_x

Inv == x < 1

THEOREM Spec => []Inv
```