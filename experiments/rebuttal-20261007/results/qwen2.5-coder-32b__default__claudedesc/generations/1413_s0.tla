------------------------------- MODULE Github790 -------------------------------
EXTENDS Naturals

CONSTANTS

VARIABLES a

Init == a = 0

Next == TRUE

Spec == Init /\ [][Next]_<<a>>

AlwaysTrue == <>TRUE => <>[]TRUE

=============================================================================