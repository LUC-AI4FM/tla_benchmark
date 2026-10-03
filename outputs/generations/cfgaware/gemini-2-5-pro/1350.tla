---- MODULE SingleCounter ----
EXTENDS Naturals

VARIABLES x

Init == x = 1

Next ==
    \/ (x < 5 /\ x' = x + 1)
    \/ (x = 5 /\ x' = x)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

Liveness == <>([](x = 5))

=============================================================================