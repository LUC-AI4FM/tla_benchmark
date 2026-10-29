---- MODULE SmallCounter ----
EXTENDS Naturals

VARIABLES x

vars == << x >>

Init == x = 0

Increment == /\ x < 3
             /\ x' = x + 1

Stutter == /\ x >= 3
           /\ x' = x

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_x

TypeOK == x \in Nat

Bounded == x <= 3

====