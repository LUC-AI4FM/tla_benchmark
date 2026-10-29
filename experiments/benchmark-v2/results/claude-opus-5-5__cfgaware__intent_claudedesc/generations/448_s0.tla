---- MODULE VarExpr ----
EXTENDS Naturals

VARIABLE x

xplus1 == x + 1

Init == x \in 0..3

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

TypeOK == x \in Nat
====