---- MODULE CounterLeadsToStable ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 1

Next == x < 5 /\ x' = x + 1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == x \in 1..5

Liveness == (x = 1) ~> [](x = 5)

====