```
MODULE SingleVariableStateMachine
VARIABLE x

Switch(x) == ~x

A == x' = Switch(x)

B == x' = Switch(x)

Next == A \/ B

Init == x = FALSE
```