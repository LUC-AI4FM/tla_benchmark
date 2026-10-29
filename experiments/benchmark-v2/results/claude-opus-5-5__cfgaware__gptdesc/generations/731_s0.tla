---- MODULE Counter ----
EXTENDS Naturals

CONSTANT UpperBound

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

Invariant == x < UpperBound

Constraint == x < UpperBound

====