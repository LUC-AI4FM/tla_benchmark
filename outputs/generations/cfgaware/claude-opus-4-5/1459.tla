---------------------------- MODULE spec ----------------------------

EXTENDS Naturals

CONSTANT Limit

VARIABLE x

Init == x = 0

Next == 
    IF x < Limit 
    THEN x' = x + 1
    ELSE UNCHANGED x

Spec == Init /\ [][Next]_x

=============================================================================