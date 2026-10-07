----------------------------- MODULE FactorialMachine -----------------------------

EXTENDS Naturals

CONSTANTS D

VARIABLES x

RECURSIVE fact(_)

fact(n) ==
  IF n = 0 THEN 1 ELSE n * fact(n - 1)

A ==
  x' = fact(3)

B ==
  x' = fact(9)

Next ==
  A \/ B

Init ==
  x = 0

TypeOK ==
  x \in Nat

Spec ==
  Init /\ [][Next]_<<x>>

=============================================================================