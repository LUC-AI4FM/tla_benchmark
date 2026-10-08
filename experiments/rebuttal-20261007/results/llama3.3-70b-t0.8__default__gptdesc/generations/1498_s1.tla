```
MODULE SingleVariableStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x

Switch(x) == ~x

A == (x' = Switch(x))

B == (x' = Switch(x))

Init == (x = FALSE)

Next == (A \/ B)

Spec == Init /\ [][Next]_
```