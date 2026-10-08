------------------------------- MODULE MinimalSpec -------------------------------
EXTENDS Integers

CONSTANTS 
    \* No constants needed for this simple example

VARIABLES x

Init == x = 0

Next == TRUE -> UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

=============================================================================