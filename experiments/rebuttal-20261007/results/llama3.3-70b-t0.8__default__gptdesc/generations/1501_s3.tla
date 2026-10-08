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
Note: The `THEOREM` statement is used to specify a property that should be verified by the model checker, but in this case, it's just verifying that the initial condition `Init` is always true. In a real specification, you would typically have more meaningful properties to verify.