------------------------------ MODULE SingleVarTS ------------------------------

EXTENDS Naturals

CONSTANT Limit
VARIABLE x

Init == x = 0

Next == /\ x < Limit
        /\ x' = x + 1

Spec == Init /\ [][Next]_x

=============================================================================