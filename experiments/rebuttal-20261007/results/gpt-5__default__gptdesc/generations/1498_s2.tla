------------------------------ MODULE BooleanToggle ------------------------------

EXTENDS TLC

CONSTANTS DUMMY

VARIABLES x

Switch(val) == ~val

Init == x = FALSE

A == x' = Switch(x)
B == x' = Switch(x)

Next == A \/ B

Spec == Init /\ [][Next]_x

=============================================================================