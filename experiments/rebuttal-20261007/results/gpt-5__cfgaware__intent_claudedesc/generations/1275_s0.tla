---- MODULE ExistInitRestrict ----
EXTENDS Integers

VARIABLES x

Init ==
  \E y \in 0..1:
    x = y /\ x < 1

Next ==
  UNCHANGED x

Spec ==
  Init /\ [] [Next]_x

Inv ==
  x < 1
====