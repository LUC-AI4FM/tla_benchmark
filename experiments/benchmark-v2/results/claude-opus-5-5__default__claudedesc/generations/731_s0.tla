---- MODULE Counter ----
EXTENDS Naturals, TLC

ASSUME PrintT("IOUtilsTests!C!b!Counter")

CONSTANT UpperBound

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_vars

Constraint == x < UpperBound

Inv == x < UpperBound

TypeOK == x \in Nat
====