---------------------------- MODULE Minimal ----------------------------
EXTENDS Naturals

VARIABLES x

Init == x = 0

Next == x' = x

Spec == Init /\ [][Next]_x

TypeInvariant == x \in Nat

============================================================================