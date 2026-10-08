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
TLCAssert(IsOne \in TLCGet("named states"))
TLCAssert(IsDone \in TLCGet("named states"))
TLCAssert(WrapAround \in TLCGet("named states"))

Fairness == SF_VARIABLES
```
Note: The `THEOREM` statements are used to specify the temporal properties, and the `TLCGet` and `TLCAssert` statements are specific to the TLC model checker. The `Fairness` statement is included for completeness but does not affect the behavior of this specification since there are no weak or strong fairness conditions mentioned in the problem description.