----------------------------- MODULE BooleanSwitch -----------------------------
EXTENDS TLC

CONSTANTS UNUSED

VARIABLES x

Switch(v) == ~v

A == x' = Switch(x)
B == x' = Switch(x)

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_<<x>>
=============================================================================