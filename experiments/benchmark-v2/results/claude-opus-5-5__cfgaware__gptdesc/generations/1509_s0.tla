---------------------------- MODULE RecFunSpec ----------------------------
EXTENDS Naturals

VARIABLE x

vars == x

\* Recursively defined function over {1,2,3,4,5}
F[i \in {1, 2, 3, 4, 5}] == IF i = 1 THEN 1 ELSE i + F[i - 1]

\* Action indexed by {1,2,3}
N(i) == /\ i \in {1, 2, 3}
        /\ x' = F[i]

Init == x = F[1]

Next == \E i \in {1, 2, 3} : N(i)

Spec == Init /\ [][Next]_x

Inv == x \in {F[j] : j \in {1, 2, 3}}

=============================================================================