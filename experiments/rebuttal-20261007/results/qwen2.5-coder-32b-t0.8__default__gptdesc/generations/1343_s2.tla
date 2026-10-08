------------------------------- MODULE TrivialSystem -------------------------------

EXTENDS TLC, Integers

CONSTANTS 
    \* No constants needed for this trivial system

VARIABLES x, y

Init == /\ x = 0
        /\ y = 0
        /\ x = y

Next == TRUE \* Stuttering steps only, so no change in state

Spec == Init /\ [][Next]_<<x, y>>

=============================================================================