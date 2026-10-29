---------------------------- MODULE B ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Switch(v) == ~v

Init == x = FALSE

A == x' = Switch(x)

B == x' = Switch(x)

Next == A \/ B

Spec == Init /\ [][Next]_vars

TypeOK == x \in BOOLEAN
==================================================================