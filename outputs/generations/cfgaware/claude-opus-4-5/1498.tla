---------------------------- MODULE Specification ----------------------------

VARIABLE x

Switch == x' = ~x

Init == x = FALSE

A == Switch

B == Switch

Next == A \/ B

=============================================================================