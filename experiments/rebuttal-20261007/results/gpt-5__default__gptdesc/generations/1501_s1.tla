----------------------------- MODULE FactorialMachine -----------------------------
EXTENDS Naturals

CONSTANTS Dummy

VARIABLES x

vars == << x >>

RECURSIVE fact(_)
fact(n) == IF n = 0 THEN 1 ELSE n * fact(n - 1)

Init == x = 0

A == x' = fact(3)
B == x' = fact(9)

Next == A \/ B

TypeInv == x \in Nat

Spec == Init /\ [][Next]_vars
=============================================================================