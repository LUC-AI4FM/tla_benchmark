---------------------------- MODULE spec ----------------------------

VARIABLE x

RECURSIVE F(_)

F(n) == IF n = 1 THEN 1
        ELSE n * F(n - 1)

N(i) == x' = x + i

Init == x = 1

Next == \E i \in {1, 2, 3} : N(i)

Spec == Init /\ [][Next]_x

Inv == x <= F(5)

=============================================================================