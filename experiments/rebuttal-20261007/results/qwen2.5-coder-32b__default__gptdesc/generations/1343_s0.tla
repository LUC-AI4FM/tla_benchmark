------------------------------- MODULE TrivialSystem -------------------------------
EXTENDS TLC

CONSTANTS 
    \* No constants defined in this system

VARIABLES x, y

Init == /\ x = 0
        /\ y = 0
        /\ x = y

Next == TRUE

Spec == Init /\ [][Next]_<<x, y>>

=============================================================================