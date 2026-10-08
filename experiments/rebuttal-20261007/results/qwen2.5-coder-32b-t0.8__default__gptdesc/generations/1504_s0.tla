------------------------------- MODULE TrivialSystem -------------------------------

EXTENDS TLC, BOOLEAN

CONSTANTS 
    \* No constants defined

VARIABLES u1

Init == u1 = TRUE

Next == /\ UNCHANGED <<u1>>
        /\ ENABLED Next

Prop == ENABLED Next

Spec == Init /\ [][Next]_<<u1>>

=============================================================================