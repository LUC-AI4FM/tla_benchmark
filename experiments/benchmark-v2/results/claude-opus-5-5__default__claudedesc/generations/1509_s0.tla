---- MODULE I ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

D == {1, 2, 3, 4, 5}

F[i \in D] == IF i = 1 THEN 1 ELSE F[i - 1] + 1

Init == x \in D

N[i \in {1, 2, 3}] == UNCHANGED <<x>>

Next == \E i \in {1, 2, 3} : N[i]

Spec == Init /\ [][Next]_vars

TypeOK == x \in D

Inv == \E i \in DOMAIN F : F[i] = x

THEOREM Spec => [](TypeOK /\ Inv)
====