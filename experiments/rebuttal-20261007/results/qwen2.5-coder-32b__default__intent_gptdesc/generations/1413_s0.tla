------------------------------- MODULE TautologyDetector -------------------------------
EXTENDS TLC, Integers

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES 
    state

Init == state = TRUE

Next == /\ UNCHANGED state

Spec == Init /\ [][Next]_<<state>>

\* Invariants
TypeOK == state \in {TRUE}

\* Liveness property: if the proposition (state = TRUE) is reachable, it must hold always after some point
Liveness == <>[](state = TRUE)

THEOREM Spec => Liveness

=============================================================================