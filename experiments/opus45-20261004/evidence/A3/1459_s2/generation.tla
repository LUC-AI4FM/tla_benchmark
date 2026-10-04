---------------------------- MODULE SmallCounter ----------------------------

EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == x < 3 /\ x' = x + 1

Spec == Init /\ [][Next]_x

TypeInvariant == x \in Nat

BoundInvariant == x <= 3

=============================================================================