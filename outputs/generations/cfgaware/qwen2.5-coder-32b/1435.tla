------------------------------- MODULE TrivialSystem -------------------------------

CONSTANTS
    x \* This will be a variable, not a constant, but TLA+ requires us to list it here.

VARIABLES
    x

Init == x = 0

Next == TRUE

Spec == Init /\ [][Next]_<<x>>

=============================================================================