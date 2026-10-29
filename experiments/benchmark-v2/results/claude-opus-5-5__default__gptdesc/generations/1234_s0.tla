---- MODULE Test ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 5

Spec == Init /\ [][Next]_x

TypeOK == x \in 0..4

Prop == [][x' = (x + 1) % 5]_x

THEOREM Spec => []TypeOK
THEOREM Spec => Prop
====