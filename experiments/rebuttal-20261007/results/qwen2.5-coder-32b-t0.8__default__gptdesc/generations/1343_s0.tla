---- MODULE TrivialSystem ----

EXTENDS TLC

CONSTANTS 

VARIABLES x, y

Init == /\ x = 0
        /\ y = 0
        /\ x = y

Next == TRUE

Spec == Init /\ [] [][Next]_<<x, y>>

====