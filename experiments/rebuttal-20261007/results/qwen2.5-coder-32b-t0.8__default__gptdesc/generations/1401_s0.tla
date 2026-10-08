---- MODULE CounterSystem ----

EXTENDS Naturals, TLC

CONSTANTS outerX

VARIABLES x

MODULE InnerModule
    VARIABLES x
    VARIABLE_INIT x = 0
    INNER_Init == TRUE
    INNER_Next ==
        \/ /\ x < 3
           /\ x' = x + 1
        \/ x' = x
    INNER_Spec == SPECIFICATION INNER_Init /\ [][INNER_Next]_<<x>>
    WF_INNER_Next == WF_x(INNER_Next)
END MODULE

INSTANCE InnerModule WITH outerX <- x

Init == outerX = 0

Next ==
    \/ /\ x < 3
       /\ \E nextX \in {x + 1} : outerX' = nextX
    \/ /\ x >= 3
       /\ outerX' = outerX

Spec == Init /\ [][Next]_<<outerX>> /\ WF_x(Next)

LIVENESS_PROPERTY == <>[](outerX = 3)

====