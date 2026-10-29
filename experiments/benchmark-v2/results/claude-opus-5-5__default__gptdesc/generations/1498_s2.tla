---- MODULE Switch ----
EXTENDS Naturals

VARIABLE x

vars == << x >>

Switch(v) == ~v

TypeOK == x \in BOOLEAN

Init == x = FALSE

A == x' = Switch(x)

B == x' = Switch(x)

Next == A \/ B

Spec == Init /\ [][Next]_vars

====