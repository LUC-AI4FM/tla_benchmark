---- MODULE CountToFive ----
EXTENDS Naturals

VARIABLES x

vars == <<x>>

Init == x = 1

Increment == /\ x < 5
             /\ x' = x + 1

Stutter == /\ x = 5
           /\ UNCHANGED x

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == x \in 1..5

Liveness == (x = 1) ~> [](x = 5)

EventuallyAlwaysFive == <>[](x = 5)

THEOREM Spec => []TypeOK
THEOREM Spec => Liveness
====