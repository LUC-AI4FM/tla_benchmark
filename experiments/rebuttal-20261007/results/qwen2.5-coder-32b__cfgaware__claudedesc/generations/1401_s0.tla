------------------------------- MODULE Github725b -------------------------------

CONSTANTS outerX

VARIABLES x

MODULE Inner725b
    VARIABLE x
    CONSTANT x

    Step == IF x < 3 THEN x' = x + 1 ELSE UNCHANGED x
    WF_x(Act) == << Act >>

END MODULE

INSTANCE Inner725b WITH x <- outerX AS Svc

Init == outerX = 0

Step == \/ Svc!Step
        \/ \A v \in S UNION {outerX} : v' = v

Spec ==
    /\ Init
    /\ [][Step]_<<Svc!WF_x(Svc!Step)>>
    /\ <>(outerX = 3)

Prop == Spec => <>(outerX = 3)

===============================================================================