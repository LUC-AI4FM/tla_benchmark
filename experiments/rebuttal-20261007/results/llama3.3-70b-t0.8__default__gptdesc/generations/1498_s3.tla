```
MODULE SingleVariableStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x

Switch(x) == IF x THEN FALSE ELSE TRUE

A == (x' = Switch(x))

B == (x' = Switch(x))

Init == (x = FALSE)

Next == (A \/ B)

Spec == Init /\ [][Next]_
```