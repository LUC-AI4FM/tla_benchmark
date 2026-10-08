---- MODULE TrivialSystem ----

EXTENDS TLC, Integers

CONSTANTS 
    \* No constants defined

VARIABLES x, y

Init == /\ x = 0
        /\ y = 0
        /\ x = y

Next == TRUE

Spec == Init /\ [] [][Next]_<<x, y>>

====