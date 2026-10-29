---- MODULE ModCounter ----
EXTENDS Naturals

VARIABLE x

InitC == x = 0

NextC == x' = (x + 1) % 6

Spec == InitC /\ [][NextC]_x

TypeOK == x \in Nat

THEOREM Spec => []TypeOK

THEOREM Spec => [](x \in Nat)

THEOREM 1 + 1 = 2
====