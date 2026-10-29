---- MODULE OuterCounter ----
EXTENDS Naturals

VARIABLE outerX

---- MODULE Inner ----
EXTENDS Naturals

VARIABLE x

Step == x < 3 /\ x' = x + 1

Fairness == WF_x(Step)
====