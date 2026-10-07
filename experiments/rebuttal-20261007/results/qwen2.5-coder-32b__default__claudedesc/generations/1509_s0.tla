------------------------------- MODULE I -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES x

F[i] == IF i = 1 THEN 1 ELSE F[i-1] + 1

Init == x \in {1,2,3,4,5}

Next == \/ UNCHANGED <<x>>
        \/ \E i \in {1,2,3} : N[i] /\ UNCHANGED <<x>>

Spec == Init /\ [][Next]_<<x>>

Inv == \E i \in DOMAIN F : F[i] = x
======================================================================