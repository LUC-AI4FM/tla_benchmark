---- MODULE Counter ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Init == x = 1

Increment == /\ x < 5
             /\ x' = x + 1

Stay == /\ x = 5
        /\ UNCHANGED x

Next == Increment \/ Stay

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == x \in 1..5

Liveness == (x = 1) => <>[](x = 5)

====