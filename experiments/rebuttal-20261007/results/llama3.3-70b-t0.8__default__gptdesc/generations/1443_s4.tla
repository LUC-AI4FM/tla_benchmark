```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS

VARIABLES x

Init == (x = 0)

IsOne == (x = 1)
IsDone == (x = 2)
WrapAround == (x' = 0 /\ x = 2)

Next == 
  IF IsDone THEN 
    OR [][x' = 0]_x
    OR [][x = x']_x
  ELSE 
    OR [][x' = (x + 1) % 3]_x
    OR [][x = x']_x

Spec == Init /\ [][Next]_x

THEOREM Spec => []<>IsOne
THEOREM Spec => []<>IsDone
THEOREM Spec => <><>WrapAround

TLCGet("NamedStateCover") = <<["IsOne" |-> 1, "IsDone" |-> 1, "WrapAround" |-> 1]>>
```