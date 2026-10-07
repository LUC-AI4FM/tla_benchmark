------------------------------- MODULE HourClockLiveness -------------------------------
EXTENDS HourClock

CONSTANTS HCnxt, HCini

VARIABLES hr

Init == HCini

Next == HCnxt

Spec == HC /\ WF_hr(HCnxt)

LSpec == Spec

THEOREM LSpec => []<><<HCnxt>>_hr
THEOREM LSpec => \A n \in 1..12 : []<>(hr = n)
THEOREM LSpec => []HCini
================================================================================