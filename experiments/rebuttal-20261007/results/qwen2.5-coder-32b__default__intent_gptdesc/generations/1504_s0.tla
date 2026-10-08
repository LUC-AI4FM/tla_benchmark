------------------------------- MODULE SimpleReactiveSystem -------------------------------
EXTENDS TLC

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES 
    boolState

Init == boolState = TRUE

Next == UNCHANGED boolState

Spec == Init /\ [][Next]_<<boolState>>

InvariantBoolTrue == boolState = TRUE

LivenessNextEnabled == [](<>[] Next)

THEOREM Spec => [] InvariantBoolTrue
THEOREM Spec => LivenessNextEnabled
================================================================================