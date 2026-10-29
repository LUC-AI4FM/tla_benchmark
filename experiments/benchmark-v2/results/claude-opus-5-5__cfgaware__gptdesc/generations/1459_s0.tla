---------------------------- MODULE SmallCounter ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 0

Inc == /\ x < 3
       /\ x' = x + 1

Stutter == /\ x >= 3
           /\ UNCHANGED x

Next == Inc \/ Stutter

Spec == Init /\ [][Next]_x

TypeOK == x \in Nat

Limit == x <= 3

=============================================================================