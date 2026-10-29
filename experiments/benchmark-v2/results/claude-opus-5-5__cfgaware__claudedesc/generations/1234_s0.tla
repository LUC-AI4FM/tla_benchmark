---- MODULE Counter ----
EXTENDS Naturals

\* Simple modular counter, intended for testing parametrized instantiation.

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 5

Spec == Init /\ [][Next]_x

====