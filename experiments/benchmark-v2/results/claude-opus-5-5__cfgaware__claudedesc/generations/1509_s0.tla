---- MODULE I ----
EXTENDS Naturals

VARIABLE x

F[i \in {1,2,3,4,5}] == IF i = 1 THEN 1 ELSE F[i-1] + 1

Init == x \in {1,2,3,4,5}

N[i \in {1,2,3}] == UNCHANGED <<x>>

Next == \E i \in {1,2,3} : N[i]

Spec == Init /\ [][Next]_<<x>>

Inv == \E i \in DOMAIN F : F[i] = x
====