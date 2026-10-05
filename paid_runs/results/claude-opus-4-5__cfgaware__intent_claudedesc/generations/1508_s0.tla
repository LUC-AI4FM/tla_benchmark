---------------------------- MODULE specification ----------------------------

EXTENDS Naturals

CONSTANTS K

VARIABLES x

TypeOK == x \in 0..5

Init == x = 0

Next == 
    \/ x' = K
    \/ x' \in 1..3
    \/ x' = 10
    \/ (x = 0 /\ x' = 1)
    \/ (x = 1 /\ x' = 2)

Invariant == TypeOK /\ x = 0

Spec == Init /\ [][Next]_x /\ Invariant

Correctness == Init /\ Invariant /\ [][Next]_x

=============================================================================