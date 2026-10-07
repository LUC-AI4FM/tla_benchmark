MODULE Inner725b
VARIABLE x

Step ==
    /\ x < 3
    /\ x' = x + 1

Fairness == WF_x(Step)

MODULE Github725b
EXTENDS Integers, TLC

VARIABLE outerX

Init == outerX = 0

Next ==
    Svc!Step \/ (¬Enabled(Svc!Step) /\ outerX' = outerX)

Spec == Init /\ [][Next]_(outerX) /\ Svc!Fairness

Prop == <> (outerX = 3)

INSTANCE Inner725b AS Svc WITH [x |-> outerX]