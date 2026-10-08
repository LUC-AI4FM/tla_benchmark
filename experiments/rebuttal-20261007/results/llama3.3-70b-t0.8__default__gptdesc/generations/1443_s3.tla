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

THEOREM Spec => []IsOne
THEOREM Spec => <>IsDone
THEOREM Spec => <>(WrapAround)

TLCGet("named_states") = <<IsOne, IsDone, WrapAround>>
\* Assert that each named predicate is counted once.
Assert == 
  /\ TLCGet("named_states")[IsOne] = 1
  /\ TLCGet("named_states")[IsDone] = 1
  /\ TLCGet("named_states")[WrapAround] = 1

THEOREM Spec => []Assert
```