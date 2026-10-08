------------------------------- MODULE SingleVarSM -------------------------------
EXTENDS TLC

VARIABLE x

Switch(v) == ~v

A == x' = Switch(x)
B == x' = Switch(x)

Next == A \/ B

Init == x = FALSE

Spec == Init /\ [][Next]_<<x>>

=============================================================================