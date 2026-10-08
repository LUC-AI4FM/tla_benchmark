----------------------------- MODULE BooleanStateMachine -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    ActionSet

VARIABLES x

Switch ==
    \E a \in ActionSet: x' = ~x

A == Switch

B == Switch

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_<<x>>

=============================================================================