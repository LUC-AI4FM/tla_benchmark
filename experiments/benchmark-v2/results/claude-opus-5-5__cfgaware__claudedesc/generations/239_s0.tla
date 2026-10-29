---- MODULE Test1623 ----
EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat

VARIABLE x

Init == x = N

Next == \/ (x > 0 /\ x' = x - 1)
        \/ (x = 0 /\ x' = x)

Spec == Init /\ [][Next]_x

Inv == x >= 0
====