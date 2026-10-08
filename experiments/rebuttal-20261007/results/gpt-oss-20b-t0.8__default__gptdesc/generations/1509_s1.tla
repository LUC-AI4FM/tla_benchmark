MODULE SmallSpec
EXTENDS Naturals

VARIABLE x

D == 1..5

F(i) ==
    IF i = 1 THEN 1 ELSE F(i-1)+1

N(j) == x' = F(j)

Init == x = 1

Next == ∃j ∈ {1,2,3} : N(j)

Inv == ∃i ∈ D : x = F(i)

Spec == Init /\ []Inv /\ [][Next]_x