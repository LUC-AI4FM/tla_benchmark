---- MODULE Minimal ----
VARIABLES x

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [][Next]_x
==========================