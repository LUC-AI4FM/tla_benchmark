---- MODULE Test ----
EXTENDS Naturals

\* Test of parametrized INSTANCE

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 5

Spec == Init /\ [][Next]_x
====