---- MODULE CounterMod6 ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

NextC == x' = (x + 1) % 6

Spec == Init /\ [][NextC]_x

TypeOK == x \in Nat

THEOREM Spec => []TypeOK

THEOREM [](x \in Nat)

THEOREM 1 + 1 = 2
====