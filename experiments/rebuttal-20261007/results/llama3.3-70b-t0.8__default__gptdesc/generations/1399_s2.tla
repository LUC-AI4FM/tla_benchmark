```
MODULE OneVariableBooleanStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
THEOREM Spec => <>[]~x
```