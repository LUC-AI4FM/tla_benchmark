------------------------------- MODULE B -------------------------------
EXTENDS TLC

CONSTANTS A, B

VARIABLES x

Switch == x' = ~x

Init == x = FALSE

Next == \/ A -> Switch
        \/ B -> Switch

Spec == INIT /\ [][Next]_<<A, B>>

=============================================================================