------------------------------- MODULE BoolStateMachine -------------------------------
EXTENDS Integers

CONSTANTS 
    TRUE, FALSE

VARIABLES 
    x

Init == x = TRUE

Next == x' = ~x

Spec == /\ Init
        /\ [][Next \/ UNCHANGED x]_<<x>>

StatePredicates ==
    \/ x = TRUE
    \/ x = FALSE
================================================================================