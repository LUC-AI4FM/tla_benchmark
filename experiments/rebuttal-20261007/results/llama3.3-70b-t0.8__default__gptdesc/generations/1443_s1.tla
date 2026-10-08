```
MODULE SmallStateMachine
EXTENDS Integers
CONSTANTS 
VARIABLES x

Init == (x = 0)

IsOne == (x = 1)
IsDone == (x = 2)
WrapAround == (x' = 0 /\ x = 2)

Next == (
          \/ (x' = (x + 1) % 3)
          \/ (x' = x)
        )

Spec == Init /\ [][Next]_x

THEOREM Spec => []IsOne
THEOREM Spec => <>IsDone
THEOREM Spec => <>(WrapAround)

TLCGet("named states") = <<IsOne, IsDone, WrapAround>>
TLCAssert(IsOne \in TLCGet("named states"))
TLCAssert(IsDone \in TLCGet("named states"))
TLCAssert(WrapAround \in TLCGet("named states"))

Fairness == SF_VARIABLES
```
Note: The provided TLA+ specification includes a check using `TLCGet` and `TLCAssert`, which are specific to the TLC model checker. This will only work when running the specification with TLC, not with other tools or in general TLA+ proofs. 

Additionally, please note that the fairness condition is defined as `SF_VARIABLES` (strong fairness for all variables), but this might need adjustments based on the actual requirements of your system, which could require weak fairness (`WF_VARIABLES`) or specific fairness conditions for certain actions. Always ensure that the specified fairness conditions align with the expected behavior of your system.