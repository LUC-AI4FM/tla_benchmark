------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals

CONSTANT Limit

VARIABLE x

Init == x = 0

Next ==
  \/ (x < Limit /\ x' = x + 1)
  \/ (x' = x)

Spec == Init /\ [] Next
=============================================================================