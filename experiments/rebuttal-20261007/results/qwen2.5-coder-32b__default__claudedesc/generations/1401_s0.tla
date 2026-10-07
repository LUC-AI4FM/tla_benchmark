------------------------------- MODULE Github725b -------------------------------
EXTENDS Naturals, TLC

CONSTANTS outerX

VARIABLES x

MODULE Inner725b
    VARIABLE x
    CONSTANT x
    VARIABLES stepEnabled

    Init == x = 0

    Step == \/ /\ x < 3
               /\ x' = x + 1
          \/ /\ x >= 3
               /\ x' = x

    Fairness == WF_x(Step)

END MODULE

VARIABLES outerX

INSTANCE Inner725b << outerX >>

Init == outerX = 0

Next == \/ Svc!Step
        \/ /\ ~Svc!stepEnabled
           /\ outerX' = outerX

Spec == Init /\ [][Next]_<<outerX>> /\ <><Svc!Fairness>_<<outerX>>

Prop == <>(outerX = 3)

=============================================================================