------------------------------ MODULE SingleVarSystem ------------------------------

EXTENDS Naturals

VARIABLES x

Init ==
  x = 0

Next ==
  /\ (x < 3) /\ (x' = x + 1)
  \/ (x >= 3) /\ (x' = x)

TypeOK ==
  x \in Nat

Spec ==
  Init /\ [][Next]_x

====================================================================================