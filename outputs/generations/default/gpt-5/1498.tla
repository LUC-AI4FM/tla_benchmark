------------------------------ MODULE BoolSwitch ------------------------------
EXTENDS TLC

CONSTANTS UNUSED
VARIABLES x

Switch == x' = ~x

A == Switch
B == Switch

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_x
==============================================================================