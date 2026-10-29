---- MODULE ParamInstanceTest ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' = (x + 1) % 5

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == x \in 0..4

Prop == [][x' = (x + 1) % 5]_x

THEOREM Spec => []TypeOK
THEOREM Spec => Prop
====