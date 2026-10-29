---- MODULE Counter ----
EXTENDS Naturals

CONSTANTS UpperBound

ASSUME UpperBound \in Nat

VARIABLES x

vars == <<x>>

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

Inv == x < UpperBound

Constraint == x < UpperBound

====