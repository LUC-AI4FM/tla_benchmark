---- MODULE RecursiveFactorial ----
EXTENDS Naturals

VARIABLE x

RECURSIVE F(_)
F(n) == IF n = 0 THEN 1 ELSE n * F(n - 1)

Init == x = 0

Next == \/ x' = F(3)
        \/ x' = F(5)

Spec == Init /\ [][Next]_x

====