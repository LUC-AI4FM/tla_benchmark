---- MODULE BooleanStateMachine ----
EXTENDS TLC

CONSTANTS
    \* No constants needed for this simple model

VARIABLES x

Switch ==
    ~x

A == 
    /\ TRUE
    /\ x' = Switch

B == 
    /\ TRUE
    /\ x' = Switch

Init ==
    x = FALSE

Next ==
    \/ A
    \/ B

Spec ==
    Init /\ [][Next]_<<x>>
========================================