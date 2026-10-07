------------------------------- MODULE LiveHourClock -------------------------------

EXTENDS HourClock

LSpec == HC /\ WF_hr(HCnxt)

Init == HCini
Next == HCnxt
Spec == LSpec

AlwaysTick == []<><<HCnxt>>_hr

AllTimes == \A n \in 1..12 : []<>(hr = n)

TypeInvariance == []HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

=============================================================================