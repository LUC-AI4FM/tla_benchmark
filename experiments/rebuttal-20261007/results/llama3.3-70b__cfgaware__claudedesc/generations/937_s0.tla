--------------------------- MODULE HourClockLiveness ---------------------------
EXTENDS HourClock

VARIABLE hr

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

WF_hr == WF_vars(HCnxt, hr)

LSpec == HC \* WF_hr

AlwaysTick == []<><<HCnxt>>_hr
AllTimes == \A n \in 1..12 : []<>(hr = n)
TypeInvariance == []HCini

THEOREM LSpec => AlwaysTick
THEOREM LSpec => AllTimes
THEOREM LSpec => TypeInvariance

=============================================================================