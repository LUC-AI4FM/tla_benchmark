------------------------------- MODULE TestModule -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Op, Id, Forty2

VARIABLES x

Init == x = 0

Next == /\ x' \in Op(x)

Spec == Init /\ [][Next]_<<x>>

=============================================================================