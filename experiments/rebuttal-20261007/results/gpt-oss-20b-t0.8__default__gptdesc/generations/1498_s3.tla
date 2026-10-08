MODULE BoolStateMachine
EXTENDS TLC

VARIABLES x

Switch(y) == ~y

A == /\ x' = Switch(x)

B == /\ x' = Switch(x)

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_x