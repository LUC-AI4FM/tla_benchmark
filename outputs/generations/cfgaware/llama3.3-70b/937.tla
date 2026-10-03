--------------------------- MODULE HourClockLiveness ---------------------------
EXTENDS Integers, HourClock

VARIABLE hr

HCnxt == hr' = (hr + 1) % 12
WF_hr == WF_vars({hr}, HCnxt)
LSpec == HC /\ [][Next]_hr /\ WF_hr

AlwaysTick == <>[]<>(hr # 0)
AllTimes == \A i \in 1..12 : <>[]<>(hr = i)
TypeInvariance == []HC_type

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance
=============================================================================