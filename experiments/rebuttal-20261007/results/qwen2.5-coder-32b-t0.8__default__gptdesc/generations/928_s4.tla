---- MODULE HC2 ----
EXTENDS HourClock

CONSTANTS hr

VARIABLES hour

HCnxt2 == hour' = (hour % 12) + 1

Init == HCini

Next == HCnxt2

Spec ==
    Init /\ [][Next]_<<hour>>

THEOREM Spec = HC
====