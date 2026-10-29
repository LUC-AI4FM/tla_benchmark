---- MODULE Counter ----
EXTENDS Naturals

CONSTANT UpperBound

ASSUME UpperBound \in Nat

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_vars

Inv == x < UpperBound

Constraint == x < UpperBound

TypeOK == x \in Nat

====