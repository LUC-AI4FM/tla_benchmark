------------------------------ MODULE RecFactDemo ------------------------------
EXTENDS Naturals

RECURSIVE fact(n)

fact(n) == IF n = 0 THEN 1 ELSE n * fact(n-1)

VARIABLE x

Init == x = 0

Next ==
    \/ x' = fact(5)
    \/ x' = fact(3)

Spec == Init /\ [][Next]_x
=============================================================================