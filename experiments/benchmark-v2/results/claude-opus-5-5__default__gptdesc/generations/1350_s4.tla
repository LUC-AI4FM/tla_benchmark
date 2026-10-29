---- MODULE CountToFive ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 1

Next == IF x < 5
           THEN x' = x + 1
           ELSE x' = x

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == x \in 1..5

Liveness == (x = 1) => <>[](x = 5)

THEOREM Spec => []TypeOK
THEOREM Spec => Liveness
====