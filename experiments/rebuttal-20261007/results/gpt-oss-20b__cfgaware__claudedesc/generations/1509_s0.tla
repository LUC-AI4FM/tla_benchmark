------------------------------ MODULE I ------------------------------
EXTENDS Naturals

VARIABLE x

Init == x \in 1..5

RECURSIVE F/1
F(i) == IF i = 1 THEN 1 ELSE F(i-1)+1

N(i) == UNCHANGED <<x>>

Next == \/ i \in 1..3 : N(i)

Inv == \E i \in 1..5 : F(i) = x

Spec == Init /\ [][Next]_<<x>>
=============================================================================