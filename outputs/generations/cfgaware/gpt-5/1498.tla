----------------------------- MODULE BoolSwitcher -----------------------------

VARIABLES x

Switch(v) == ~v

Init == x = FALSE

A == x' = Switch(x)

B == x' = Switch(x)

Next == A \/ B

=============================================================================