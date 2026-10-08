------------------------------- MODULE TrivialSystem -------------------------------
EXTENDS Naturals

CONSTANTS 
    \* No constants needed for this simple system

VARIABLES x

Init == x = 0

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

=============================================================================