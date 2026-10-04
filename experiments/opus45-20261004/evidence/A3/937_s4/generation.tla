---------------------------- MODULE LiveHourClock ----------------------------
EXTENDS Naturals

CONSTANT HourRange
ASSUME HourRange = 1..12

VARIABLE hr

TypeOK == hr \in HourRange

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HCini == hr \in HourRange

HC == HCini /\ [][HCnxt]_hr

LSpec == HC /\ WF_hr(HCnxt)

TicksInfinitelyOften == []<><<HCnxt>>_hr

EveryHourRecurs == \A h \in HourRange : []<>(hr = h)

AlwaysTypeOK == []TypeOK

THEOREM LSpec => TicksInfinitelyOften /\ EveryHourRecurs /\ AlwaysTypeOK

Settles == <>[](hr = 12)

CounterexampleSettles == 
    /\ hr = 1
    /\ [][HCnxt]_hr
    /\ WF_hr(HCnxt)
    /\ ~Settles

=============================================================================