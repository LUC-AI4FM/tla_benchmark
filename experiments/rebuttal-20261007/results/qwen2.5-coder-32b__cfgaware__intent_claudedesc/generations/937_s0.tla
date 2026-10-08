------------------------------- MODULE ClockSpecification ------------------------------

EXTENDS HourClock

CONSTANTS Tick

VARIABLE hour

LSpec == LiveSpec

AlwaysTick == [](<>[]Tick)

AllTimes == \A h \in 1..12: <>[](hour = h)

TypeInvariance == \A s \in State: s.hour \in 1..12

LiveSpec == Spec \/ []<>(Tick)

Spec == /\ TypeOK
        /\ [][Next]_<<hour>>
        /\ WF_next(<<hour>>)

THEOREM LiveSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

=============================================================================