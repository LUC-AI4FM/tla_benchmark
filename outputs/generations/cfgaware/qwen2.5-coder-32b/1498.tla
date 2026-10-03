------------------------------- MODULE BooleanStateMachine -------------------------------

VARIABLES x

CONSTANTS FALSE TRUE

Switch == x' := ~x

A == Switch

B == Switch

Init == x = FALSE

Next == A \/ B

=============================================================================