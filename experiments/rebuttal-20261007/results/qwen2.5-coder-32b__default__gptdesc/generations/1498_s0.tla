------------------------------- MODULE BooleanStateMachine -------------------------------
EXTENDS Naturals

CONSTANTS 
    \* No constants needed for this specification

VARIABLES x

Switch == ~x

A == x' = Switch

B == x' = Switch

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_<<x>>
=============================================================================