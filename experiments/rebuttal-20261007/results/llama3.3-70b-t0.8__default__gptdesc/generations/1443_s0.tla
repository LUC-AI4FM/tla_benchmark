```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == (x = 0)

IsOne == (x = 1)
IsDone == (x = 2)
WrapAround == (x' = 0 /\ x = 2)

Next == (x' = (x + 1) % 3)

Spec == Init /\ [][Next]_x

THEOREM Spec => []<>IsOne
THEOREM Spec => []<>IsDone
THEOREM Spec => <><>WrapAround

TLCGet("named states") = <<IsOne, IsDone, WrapAround>>
Fairness == SF_VARIABLES

THEOREM Spec => Fairness
```
Note: The TLC-specific part may need adjustments depending on the actual TLC version and configuration being used.