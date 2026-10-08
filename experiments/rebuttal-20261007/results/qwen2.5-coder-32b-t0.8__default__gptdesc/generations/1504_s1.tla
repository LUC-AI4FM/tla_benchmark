------------------------------ MODULE TrivialSystem ------------------------------

EXTENDS TLC

CONSTANTS 
    \* No constants needed for this system

VARIABLES u1

Init == u1 = TRUE

Next == /\ UNCHANGED <<u1>>

Prop == ENABLED Next

Spec == Init /\ [][Next]_<<u1>>

=============================================================================