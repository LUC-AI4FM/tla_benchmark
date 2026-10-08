------------------------------- MODULE MinimalViableSpec -------------------------------

CONSTANTS
    \* No constants are needed for this simple specification

VARIABLES
    x

Init == x = 0

Next == TRUE /\ UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

=============================================================================