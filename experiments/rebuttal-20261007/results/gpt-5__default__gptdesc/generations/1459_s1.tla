---- MODULE SmallNatTS ----
EXTENDS Naturals

CONSTANTS Dummy

VARIABLES x

Init ==
  x = 0

Next ==
  /\ x < 3
  /\ x' = x + 1

Spec ==
  Init /\ [][Next]_x

TypeOK ==
  x \in Nat

Inv ==
  /\ TypeOK
  /\ x <= 3
====