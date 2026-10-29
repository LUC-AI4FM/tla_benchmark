---- MODULE ParamInstanceTest ----
\* A test of parametrized INSTANCE (no instance is actually used here)
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 5

Spec == Init /\ [][Next]_x

TypeOK == x \in 0..4
====