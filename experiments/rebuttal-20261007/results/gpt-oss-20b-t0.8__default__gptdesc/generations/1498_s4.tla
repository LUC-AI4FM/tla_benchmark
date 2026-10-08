MODULE SingleVarSM
VARIABLES x

Init == x = FALSE

Switch(b) == ~b

A == x' = Switch(x)
B == x' = Switch(x)

Next == A \/ B

Spec == Init /\ [][Next]_{x}