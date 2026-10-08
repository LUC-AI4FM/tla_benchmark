------------------------------ MODULE RecFactorialDemo ------------------------------
EXTENDS Naturals

VARIABLES v

RECURSIVE Factorial(_)

Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n-1)

Init == v = 0

Next == (v' = Factorial(3)) \/ (v' = Factorial(4))

Spec == Init /\ [] Next
=============================================================================