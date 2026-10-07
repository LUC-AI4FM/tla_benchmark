------------------------------ MODULE BooleanSwitch ------------------------------

EXTENDS Naturals

CONSTANTS DummyConst

VARIABLES x

Switch(b) == ~b

A == x' = Switch(x)

B == x' = Switch(x)

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_x

=============================================================================