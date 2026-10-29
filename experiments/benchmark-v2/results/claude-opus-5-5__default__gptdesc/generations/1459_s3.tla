---------------------------- MODULE SmallCounter ----------------------------
EXTENDS Naturals

VARIABLE x

vars == << x >>

TypeOK == x \in Nat

Init == x = 0

Increment == /\ x < 3
             /\ x' = x + 1

Stutter == /\ x >= 3
           /\ x' = x

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_x

\* Safety invariants
Bounded == x <= 3

Inv == TypeOK /\ Bounded

=============================================================================