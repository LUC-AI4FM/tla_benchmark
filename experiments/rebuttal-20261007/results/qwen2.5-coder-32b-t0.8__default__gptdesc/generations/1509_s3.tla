---------------------------- MODULE SmallSystem ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    F

VARIABLES x

Init == x \in {1, 2, 3, 4, 5}

F[1] == 2
F[n \in {2, 3, 4}] == F[n - 1] + 1
F[5] == 1

N_1[x] == x' = F[x]
N_2[x] == x' = x
N_3[x] == x' \in {1, 2, 3, 4, 5}

Next == \/ \E i \in {1, 2, 3} : N_i[x]

Inv == x \in {1, 2, 3, 4, 5} /\ F[x] \in {1, 2, 3, 4, 5}

Spec == Init /\ [][Next]_<<x>>

=============================================================================