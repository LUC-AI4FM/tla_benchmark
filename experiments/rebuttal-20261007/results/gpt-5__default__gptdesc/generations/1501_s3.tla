----------------------------- MODULE SmallFactorial -----------------------------
EXTENDS Naturals

CONSTANTS DummyConst

VARIABLES x

RECURSIVE fact(_)
fact(n) == IF n = 0 THEN 1 ELSE n * fact(n - 1)

TypeInv == x \in Nat

Init == x = 0

A == x' = fact(3)
B == x' = fact(9)

Next == A \/ B

Vars == << x >>

Spec == Init /\ [][Next]_Vars
=============================================================================