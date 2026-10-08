----------------------------- MODULE ConstrainedNextDemo -----------------------------

EXTENDS Integers

VARIABLES x

Init ==
  x = 23

Next ==
  \/ /\ x' \in {0, 1}
     /\ x' > 0
  \/ UNCHANGED x

Spec ==
  Init /\ [][Next]_x

TypeOK ==
  x \in Int

NoZero ==
  x # 0

Inv ==
  NoZero

AlwaysNoZero ==
  [](x # 0)
=====================================================================================