------------------------------- MODULE I -------------------------------

CONSTANTS
    N \* This is not used in the specification but included as per requirement

VARIABLES x

DOMAIN == {1, 2, 3, 4, 5}

F[i] == IF i = 1 THEN 1 ELSE F[i - 1] + 1

Init == x \in DOMAIN

N[i] == UNCHANGED <<x>>

Next == \/ i \in {1, 2, 3} : N[i]

Spec == Init /\ [][Next]_<<x>>

Inv == \E i \in DOMAIN : F[i] = x

=============================================================================