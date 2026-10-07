------------------------------ MODULE Github790 ------------------------------

EXTENDS Naturals

VARIABLES a

Init == a = 0

Next == UNCHANGED a

Spec == Init /\ [][Next]_a

AlwaysTrue == <>TRUE => <>[]TRUE

==============================================================================