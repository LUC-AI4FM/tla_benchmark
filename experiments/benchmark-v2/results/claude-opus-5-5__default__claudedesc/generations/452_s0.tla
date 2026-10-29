---- MODULE ParamInstanceTarget ----
EXTENDS Naturals

VARIABLE x

vars == << x >>

TypeOK == x \in Nat

Init == x = 0

Next == x' = (x + 1) % 5

Spec == Init /\ [][Next]_x
====