------------------------------- MODULE HourClockLiveness -------------------------------

CONSTANTS hr \* Assuming hr is a constant representing the hour variable

VARIABLES hrclock

HC == /\ hrclock \in 1..12
    /\ \/ hrclock' = hrclock + 1
       \/ hrclock' = 1

HCnxt == HC /\ hrclock' # hrclock

WF_hr(pred) == <<hrclock>>, pred

LSpec == HC /\ WF_hr(HCnxt)

AlwaysTick == [](<>HCnxt)

AllTimes == []<>(\E t \in 1..12 : <>[](hrclock = t))

TypeInvariance == [](HC)

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

=============================================================================