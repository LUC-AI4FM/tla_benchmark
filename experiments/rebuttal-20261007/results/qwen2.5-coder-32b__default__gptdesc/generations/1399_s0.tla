------------------------------- MODULE BooleanStateMachine -------------------------------
EXTENDS TLC

CONSTANTS 
    \* No constants needed for this specification

VARIABLES 
    x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next \/ UNCHANGED x]_<<x>>

=============================================================================