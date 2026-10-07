------------------------------- MODULE TrivialSystem -------------------------------
EXTENDS TLC, Integers

CONSTANTS 
    \* No constants defined

VARIABLES x, y

Init == /\ x = 0
        /\ y = 0
        /\ y = x

Next == UNCHANGED <<x, y>>

Spec == Init /\ []Next

=============================================================================