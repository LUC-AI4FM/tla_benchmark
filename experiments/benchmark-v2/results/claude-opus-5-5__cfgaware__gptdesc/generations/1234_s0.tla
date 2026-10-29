---- MODULE ParamInstanceTest ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 5

Spec == Init /\ [][Next]_x

Prop == [][x' = (x + 1) % 5]_x
====