---- MODULE ModCounter ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' = (x + 1) % 6

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

Inv == x \in Nat

THEOREM SimpleArith == 2 + 2 = 4

ArithOK == 2 + 3 = 5

THEOREM Spec => []Inv
====