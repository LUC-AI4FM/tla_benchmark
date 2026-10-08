------------------------------ MODULE MinimalStatic ------------------------------
EXTENDS Naturals, TLC

VARIABLES x

Init ==
  /\ x = 0

Next ==
  UNCHANGED x

Spec ==
  Init /\ []Next
=============================================================================