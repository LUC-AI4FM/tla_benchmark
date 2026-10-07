```
MODULE HourClockLiveness
EXTENDS HourClock

CONSTANTS

VARIABLES hr

Init == (hr \in 1..12)

HCnxt == (hr' = IF hr = 12 THEN 1 ELSE hr + 1)

Next == HCnxt

Spec == Init /\ [][Next]_hr

LSpec == Spec /\ WF_hr(HCnxt)

AlwaysTick == []<><<HCnxt>>_hr
AllTimes == \A n \in 1..12 : []<>(hr = n)
TypeInvariance == [](hr \in 1..12)

THEOREM LSpec => AlwaysTick
THEOREM LSpec => AllTimes
THEOREM LSpec => TypeInvariance

=============================================================================
```
Note: The `HourClock` module is assumed to be defined elsewhere, and its contents are not included in this specification.