---- MODULE Clock12 ----
EXTENDS Naturals

VARIABLE hour

HC == INSTANCE HourClockBase WITH hour <- hour

LSpec == HC!Init /\ [][HC!Next]_hour /\ WF_hour(HC!Tick)

AlwaysTick == []<>(<HC!Tick>_hour)

AllTimes == \A h \in 1..12 : []<>(hour = h)

TypeInvariance == [](hour \in 1..12)

THEOREM LiveImpliesProperties == LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance
====