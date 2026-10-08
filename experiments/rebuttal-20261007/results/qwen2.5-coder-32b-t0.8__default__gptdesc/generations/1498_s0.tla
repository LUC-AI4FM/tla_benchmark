---- MODULE BooleanStateMachine ----

EXTENDS Naturals

CONSTANTS 
    Action

VARIABLES 
    x

Switch == IF x THEN FALSE ELSE TRUE

A == \/ Action = "A" 
     /\ x' = Switch

B == \/ Action = "B"
     /\ x' = Switch

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [][Next]_<<x>>

====