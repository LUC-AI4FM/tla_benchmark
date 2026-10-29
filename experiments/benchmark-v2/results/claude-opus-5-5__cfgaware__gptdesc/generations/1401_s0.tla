---------------------------- MODULE OuterCounter ----------------------------
EXTENDS Naturals

VARIABLE outerX

---------------------------- MODULE Inner ----------------------------
EXTENDS Naturals

VARIABLE x

Step == x < 3 /\ x' = x + 1

Fair == WF_x(Step)
=============================================================================