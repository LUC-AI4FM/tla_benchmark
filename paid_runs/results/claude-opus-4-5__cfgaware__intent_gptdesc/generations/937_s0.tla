---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLES hr

Hours == 1..12

TypeInvariance == hr \in Hours

Init == hr = 1

Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == Tick

Spec == Init /\ [][Next]_hr

LSpec == Spec /\ WF_hr(Tick)

AlwaysTick == []<><<Tick>>_hr

AllTimes == \A h \in Hours : []<>(hr = h)

THEOREM LSpec => []TypeInvariance

THEOREM LSpec => AlwaysTick

THEOREM LSpec => AllTimes

==========================================================================