------------------------------- MODULE BooleanStateMachine -------------------------------
EXTENDS Naturals

CONSTANTS TRUE, FALSE

VARIABLES x

Switch == x' = ~x

A == Switch

B == Switch

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_<<x>>
====================================================================