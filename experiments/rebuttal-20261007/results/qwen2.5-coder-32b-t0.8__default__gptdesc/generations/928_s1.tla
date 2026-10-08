------------------------------ MODULE HC2 ------------------------------

EXTENDS HourClock

CONSTANTS 
    \* Assuming no additional constants are needed beyond those in HourClock

VARIABLES hr

HCnxt2 == hr' = (hr % 12) + 1

Init == HCini

Next == HCnxt2

Spec == Init /\ [][Next]_<<hr>>

THEOREM Spec => HC

=============================================================================