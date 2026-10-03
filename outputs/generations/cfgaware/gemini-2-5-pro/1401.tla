---------------- MODULE Outer ----------------

EXTENDS Integers, TLC

VARIABLE outerX

---- MODULE Inner ----
EXTENDS Integers
VARIABLE x
Step == /\ x < 3
        /\ x' = x + 1
Fairness == WF_x(Step)
======================