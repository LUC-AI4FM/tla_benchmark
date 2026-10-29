---------------------------- MODULE OuterCounter ----------------------------
EXTENDS Naturals

VARIABLE outerX

vars == << outerX >>

---------------------------- MODULE InnerCounter ----------------------------
VARIABLE x

Step == /\ x < 3
        /\ x' = x + 1

Fairness == WF_x(Step)
=============================================================================