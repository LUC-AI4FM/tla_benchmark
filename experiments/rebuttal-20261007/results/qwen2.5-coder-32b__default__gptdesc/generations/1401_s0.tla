------------------------------- MODULE CounterSystem -------------------------------
EXTENDS Naturals

CONSTANTS outerX

VARIABLES x

InnerStep == \/ x < 3 -> x' = x + 1
             \/ TRUE  -> x' = x

Init == x = 0

Next == \/ InnerStep
        \/ /\ x >= 3
           /\ x' = x

Spec == Init /\ [][Next]_<<x>>

WF_InnerStep == WF_x(InnerStep)

Liveness == <>(x = 3)

=============================================================================