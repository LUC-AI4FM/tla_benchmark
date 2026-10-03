----------------------------- MODULE Inner -----------------------------
EXTENDS Naturals

CONSTANT Bound
VARIABLE x

Step == /\ x < Bound
        /\ x' = x + 1

Fair == WF_x(Step)
========================================================================