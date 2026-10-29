---- MODULE AssignAndGuard ----
EXTENDS Integers

VARIABLE x

Init == x = 23

Next == \E v \in {0, 1} : x' = v /\ x' > 0

Spec == Init /\ [][Next]_x

Inv == x # 0
====