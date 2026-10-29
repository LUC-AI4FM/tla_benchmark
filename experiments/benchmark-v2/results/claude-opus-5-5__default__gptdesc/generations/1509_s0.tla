---------------------------- MODULE RecursiveFcn ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

\* Recursively defined function over {1,2,3,4,5}
F[n \in {1, 2, 3, 4, 5}] == IF n = 1 THEN 1 ELSE n * F[n - 1]

\* Indexed action family over {1,2,3}
N(i) == /\ i \in {1, 2, 3}
        /\ x' = F[i]

Init == x = F[1]

Next == \E i \in {1, 2, 3} : N(i)

Spec == Init /\ [][Next]_x

\* Invariant relating x to values of F
Inv == x \in {F[j] : j \in {1, 2, 3, 4, 5}}

TypeOK == x \in Nat

THEOREM Spec => [](Inv /\ TypeOK)
=============================================================================