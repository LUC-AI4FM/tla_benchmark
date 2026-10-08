------------------------------- MODULE TrivialSystem -------------------------------

EXTENDS Integers, TLC, Sequences

CONSTANTS 
    \* No constants defined in the description

VARIABLES u1

Init == u1 = TRUE

Next == /\ UNCHANGED <<u1>>
        /\ u1' = u1

Prop == ENABLED Next

Spec == Init /\ [][Next]_<<u1>>

================================================================================