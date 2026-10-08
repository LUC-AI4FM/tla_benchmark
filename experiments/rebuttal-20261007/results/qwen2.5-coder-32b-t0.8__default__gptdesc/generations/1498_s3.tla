------------------------------- MODULE StateMachine -------------------------------
EXTENDS Integers

CONSTANTS A, B

VARIABLES x

Switch == x' = ~x

Init == x = FALSE

A == Switch

B == Switch

Next == \/ A
        \/ B

Spec == Init /\ [][Next]_<<x>>

=============================================================================