---- MODULE ParamInstanceTest ----
\* Test of parametrized INSTANCE (no actual instance used)
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 5

vars == <<x>>

Spec == Init /\ [][Next]_x

TypeOK == x \in 0..4
====