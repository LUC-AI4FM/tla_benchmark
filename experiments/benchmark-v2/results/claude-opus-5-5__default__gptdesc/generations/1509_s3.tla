---------------------------- MODULE RecursiveFcnSpec ----------------------------
EXTENDS Naturals

VARIABLES x

vars == << x >>

F[i \in {1, 2, 3, 4, 5}] == IF i = 1 THEN 1 ELSE F[i - 1] + i

N(i) == /\ i \in {1, 2, 3}
        /\ x' = F[i]

Init == x = F[1]

Next == \E i \in {1, 2, 3} : N(i)

Spec == Init /\ [][Next]_x

Inv == x \in {F[j] : j \in {1, 2, 3, 4, 5}}

TypeOK == x \in Nat

THEOREM Spec => []Inv
=============================================================================