---- MODULE CounterToFive ----
EXTENDS Naturals

VARIABLE x

Init == x = 1

Next == /\ x < 5
        /\ x' = x + 1

Spec == /\ Init
        /\ [][Next]_x
        /\ WF_x(Next)

Liveness == <>[] (x = 5)
====