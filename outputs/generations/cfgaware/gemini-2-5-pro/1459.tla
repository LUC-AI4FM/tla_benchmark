---- MODULE SimpleCounter ----
EXTENDS Naturals

VARIABLE x

Limit == 3

Init == x = 0

Next ==
    \/ (x < Limit /\ x' = x + 1)
    \/ (x >= Limit /\ x' = x)

Spec == Init /\ [][Next]_x

============================