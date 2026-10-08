---------------------------- MODULE Github725b ----------------------------
EXTENDS Integers

Inner725b == INSTANCE Inner WITH x <- outerX
VARIABLE outerX

Step == IF outerX < 3 THEN Svc!Step ELSE FALSE

Spec == outerX = 0 /\ [][Step]_outerX /\ Svc!Fairness
Prop == <> (outerX = 3)

Inner == [* ## Step -> x' = x + 1 *]
        /\ WF_x(Step)
==================================