------------------------------ MODULE Github790 ------------------------------

EXTENDS TLC

CONSTANTS foo

VARIABLES a

Init == a = 0

Next == TRUE

Spec == Init /\ [][Next]_a

AlwaysTrue == <>TRUE => <>[]TRUE

=============================================================================