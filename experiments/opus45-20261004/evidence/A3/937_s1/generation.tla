---------------------------- MODULE LiveHourClock ----------------------------
EXTENDS Naturals

CONSTANT HourSet

VARIABLE hr

HC == hr \in HourSet

HCini == hr \in HourSet

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HCSpec == HCini /\ [][HCnxt]_hr

LSpec == HCSpec /\ WF_hr(HCnxt)

TypeOK == hr \in HourSet

TicksInfinitelyOften == []<><<HCnxt>>_hr

EveryHourRecurs == \A h \in 1..12 : []<>(hr = h)

AlwaysTyped == []HC

THEOREM LSpec => TicksInfinitelyOften /\ EveryHourRecurs /\ AlwaysTyped

Settles == <>[](hr = 12)

CounterexampleSettles == 
    /\ hr = 1
    /\ [][HCnxt]_hr
    /\ []<><<HCnxt>>_hr
    /\ ~Settles

=============================================================================