------------------------------ MODULE HourClock2 ------------------------------

EXTENDS HourClock

CONSTANTS HCini

VARIABLES hr

Init == HCini

HCnxt2 == hr' = (hr % 12) + 1

Next == HCnxt \/ HCnxt2

Spec == Init /\ [][Next]_<<hr>>

THEOREM HC => HC2

=============================================================================