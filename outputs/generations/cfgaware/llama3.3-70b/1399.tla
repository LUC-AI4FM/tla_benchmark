```
MODULE OneVariableBooleanStateMachine
VARIABLE x

Init == x = TRUE

Next == x' = ~x

Stutter == x = x'

Spec == Init /\ [][Next \/ Stutter]_x

Prop == <>x
```