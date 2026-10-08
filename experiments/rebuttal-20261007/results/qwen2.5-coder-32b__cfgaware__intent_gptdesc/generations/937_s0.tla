------------------------------- MODULE HourClock -------------------------------

CONSTANTS
    \* Constants to be defined by the model checker configuration
    LSpec,
    AlwaysTick,
    AllTimes,
    TypeInvariance

VARIABLES hour

HourValues == 1..12

NextHour(h) == IF h = 12 THEN 1 ELSE h + 1

Init == hour \in HourValues

Next ==
    /\ hour' \in HourValues
    /\ hour' = NextHour(hour)

Spec ==
    Init /\ [][Next]_<<hour>>

LSpec == Spec

AlwaysTick == [](hour' # hour)

AllTimes ==
    \/ hour = 1
    \/ hour = 2
    \/ hour = 3
    \/ hour = 4
    \/ hour = 5
    \/ hour = 6
    \/ hour = 7
    \/ hour = 8
    \/ hour = 9
    \/ hour = 10
    \/ hour = 11
    \/ hour = 12

TypeInvariance == Spec /\ [](hour \in HourValues)

THEOREM TypeInvariance

THEOREM AlwaysTick

THEOREM AllTimes

=============================================================================