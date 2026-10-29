---- MODULE CycleMod6 ----
EXTENDS Naturals

VARIABLES x

vars == x

InitC == x = 0

NextC == x' = (x + 1) % 6

Init == InitC

Next == NextC

Spec == InitC /\ [][NextC]_x

TypeOK == x \in Nat

THEOREM Spec => []TypeOK

THEOREM []TypeOK => [](x \in Nat)

THEOREM 1 + 1 = 2
====