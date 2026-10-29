---- MODULE Counter ----
EXTENDS Naturals

CONSTANT UpperBound

ASSUME UpperBound \in Nat /\ UpperBound > 0

VARIABLE x

vars == <<x>>

TypeOK == x \in Nat

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_vars

Inv == x < UpperBound

Constraint == x < UpperBound

THEOREM Spec => []TypeOK
====