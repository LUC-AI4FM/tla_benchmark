------------------------------ MODULE RecSpec ------------------------------
EXTENDS Naturals

VARIABLE x

F(i) == IF i = 1 THEN 2 ELSE F(i-1)+1

N(i) == /\ i ∈ 1..3
        /\ x' = F(i)

Init == x = F(1)

Next == ∃i ∈ 1..3 : N(i)

Inv == ∃i ∈ 1..5 : x = F(i)

Spec == Init /\ [][Next]_x

=============================================================================