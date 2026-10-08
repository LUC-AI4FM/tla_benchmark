------------------------------- MODULE BooleanStateMachine -------------------------------

EXTENDS Naturals, TLC

CONSTANTS 
    -- No constants needed for this simple specification

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next \/ UNCHANGED x]_<<x>>

================================================================================