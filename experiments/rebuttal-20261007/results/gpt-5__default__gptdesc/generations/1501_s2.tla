------------------------------ MODULE FactorialMachine ------------------------------

EXTENDS Naturals

CONSTANTS
  Dummy

VARIABLES
  x

RECURSIVE fact(_)

fact(n) ==
  IF n = 0 THEN 1 ELSE n * fact(n - 1)

Init ==
  x = 0

A ==
  x' = fact(3)

B ==
  x' = fact(9)

Next ==
  A \/ B

Vars ==
  << x >>

Spec ==
  Init /\ [][Next]_Vars

TypeOK ==
  x \in Nat

Safety ==
  []TypeOK

=============================================================================