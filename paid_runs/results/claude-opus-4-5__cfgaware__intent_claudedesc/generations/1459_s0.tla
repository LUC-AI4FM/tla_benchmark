---------------------------- MODULE spec ----------------------------
EXTENDS Naturals

CONSTANT Limit

VARIABLE counter

Init == counter = 0

Next == 
    IF counter < Limit 
    THEN counter' = counter + 1
    ELSE UNCHANGED counter

Spec == Init /\ [][Next]_counter

=============================================================================