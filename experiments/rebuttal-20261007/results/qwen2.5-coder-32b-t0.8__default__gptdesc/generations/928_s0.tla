------------------------------- MODULE HC2 -------------------------------

EXTENDS HourClock, TLC

CONSTANTS hr

VARIABLES hr

HCnxt2 == hr' = (hr % 12) + 1

Init == HCini

Next == HCnxt2

Spec ==
    /\ Init
    /\ [][Next]_<<hr>>

THEOREM Spec = HC

=============================================================================