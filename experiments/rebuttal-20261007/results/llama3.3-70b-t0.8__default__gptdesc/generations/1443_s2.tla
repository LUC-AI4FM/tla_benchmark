```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == (x = 0)

IsOne == (x = 1)
IsDone == (x = 2)
WrapAround == (x' = 0 /\ x = 2)

Next == IF IsDone THEN (x' = 0) ELSE (x' = (x + 1) % 3)

Spec == Init /\ [][Next]_x

THEOREM Spec => []<>IsOne
THEOREM Spec => []<>IsDone
THEOREM Spec => <><>WrapAround

TLCGet("NamedStates") = <<IsOne, IsDone, WrapAround>>
Assert TLCGet("NamedStates") = <<1, 1, 1>>

=============================================================================
```
Note: The code uses the TLA+ language syntax. Please make sure to use a compatible tool (like TLC) for checking and running this specification.