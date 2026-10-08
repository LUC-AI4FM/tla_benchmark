------------------------------- MODULE StationarySystem -------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES x

Init == x = TRUE

Next == UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

Invariant == TRUE \* This is vacuously true as Next never changes the state

Liveness == <>[]TRUE \* Trivial liveness property, always true

=============================================================================