------------------------------- MODULE HourClockLiveness -------------------------------

EXTENDS HourClock

CONSTANTS
    \* Constants from HourClock are inherited

VARIABLES
    hr  \* Variable from HourClock is inherited

HCini == hr \in 1..12

HCnxt ==
    \/ /\ hr = 12
       /\ hr' = 1
    \/ /\ hr \in 1..11
       /\ hr' = hr + 1

LSpec == HC /\ WF_hr(HCnxt)

AlwaysTick == []<><<HCnxt>>_hr

AllTimes == \A n \in 1..12 : []<>(hr = n)

TypeInvariance == []HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

=============================================================================