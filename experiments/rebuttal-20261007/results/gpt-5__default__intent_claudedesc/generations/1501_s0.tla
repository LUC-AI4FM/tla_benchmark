----------------------------- MODULE RecursiveFactorialMachine -----------------------------

EXTENDS Naturals

CONSTANTS N1, N2

VARIABLES x

RECURSIVE Fact(_)
Fact(n) ==
  IF n = 0 THEN 1
  ELSE n * Fact(n - 1)

Init == x = 0

Next ==
  \/ x' = Fact(N1)
  \/ x' = Fact(N2)

vars == << x >>

Spec == Init /\ [] [Next]_vars

ASSUME N1 \in Nat /\ N2 \in Nat

===========================================================================================