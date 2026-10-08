------------------------------- MODULE TrivialSystem -------------------------------
EXTENDS Naturals

CONSTANTS
    \* No constants needed for this simple system

VARIABLES x

Init == x = 0

Next == TRUE /\ UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

=============================================================================