------------------------------- MODULE TrivialSystem -------------------------------

EXTENDS Integers

CONSTANTS

VARIABLES x

Init == x = 0

Next == TRUE /\ UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

================================================================================