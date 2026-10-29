---------------------------- MODULE Factorial ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

RECURSIVE fact(_)
fact(n) == IF n = 0 THEN 1 ELSE n * fact(n - 1)

TypeOK == x \in Nat

Init == x = 0

A == x' = fact(3)

B == x' = fact(9)

Next == A \/ B

Spec == Init /\ [][Next]_<<x>>

THEOREM Spec => []TypeOK
=============================================================================