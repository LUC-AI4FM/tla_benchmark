------------------------------ MODULE SmallStateMachine ------------------------------

EXTENDS Naturals

CONSTANTS fact

VARIABLES x

Init == x = 0

A == x' = fact(3)

B == x' = fact(9)

Next == A \/ B

Spec == Init /\ [][Next \/ UNCHANGED <<x>>]_<<x>>

================================================================================