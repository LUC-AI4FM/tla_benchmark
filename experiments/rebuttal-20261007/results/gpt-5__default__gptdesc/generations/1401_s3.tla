---- MODULE Inner ----
EXTENDS Naturals

VARIABLES x

Step ==
  /\ x < 3
  /\ x' = x + 1

Spec ==
  /\ [][Step]_x
  /\ WF_x(Step)

====