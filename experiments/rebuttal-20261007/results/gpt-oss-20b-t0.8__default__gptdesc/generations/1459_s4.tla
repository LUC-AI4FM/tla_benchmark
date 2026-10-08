------------------------------ MODULE SmallSystem ------------------------------
EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == /\ x < 3
        /\ x' = x + 1

Stutter == x' = x

Spec == Init /\ [] (Next \/ Stutter)

=============================================================================