---------------------------- MODULE RecursiveFactorial ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

RECURSIVE Factorial(_)
Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n - 1)

Init == x = 0

A == x' = Factorial(3)

B == x' = Factorial(5)

Next == A \/ B

Spec == Init /\ [][Next]_vars

TypeOK == x \in Nat

=============================================================================