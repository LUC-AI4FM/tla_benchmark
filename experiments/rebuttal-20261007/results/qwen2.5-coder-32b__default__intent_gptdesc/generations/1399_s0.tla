------------------------------- MODULE ToggleSystem -------------------------------
EXTENDS TLC, Integers

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES state

Init == state = TRUE

Next == \/ state' = ~state
        \/ state' = state

Spec == Init /\ [][Next]_<<state>>

InvariantStrong == \/ state = TRUE
                 \/ state = FALSE

InvariantWeak == TRUE \* Always true, just for observational comparison

TypeOK == \/ state = TRUE
          \/ state = FALSE

Liveness == <>[](\/ state' = ~state
                  \/ state' = state)

SpecWithFairness == Spec /\ WF_next(<<state>>)

THEOREM Spec => []TypeOK
THEOREM Spec => []InvariantStrong
THEOREM Spec => []InvariantWeak
THEOREM SpecWithFairness => Liveness

=============================================================================