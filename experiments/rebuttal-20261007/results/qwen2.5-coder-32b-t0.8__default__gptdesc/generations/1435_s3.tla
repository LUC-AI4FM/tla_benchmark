------------------------------ MODULE TrivialSystem ------------------------------

EXTENDS Naturals

CONSTANTS

VARIABLES x

Init == x = 0

Next == TRUE

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

=============================================================================