------------------------------ MODULE Github1037 ------------------------------
EXTENDS Naturals

VARIABLES x

Init ==
    x = 1

Next ==
    /\ x' = IF x < 5 THEN x + 1 ELSE x

Spec ==
    Init
    /\ [] [Next]_x
    /\ WF_vars(Next)

Liveness ==
    (x = 1) => <>[](x = 5)
=============================================================================