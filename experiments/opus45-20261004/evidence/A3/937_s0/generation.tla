---------------------------- MODULE LiveHourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

HCini == hr \in (1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr

LSpec == HC /\ WF_hr(HCnxt)

TypeOK == hr \in (1..12)

TicksInfinitelyOften == []<><<HCnxt>>_hr

EveryHourRecurs == \A h \in (1..12) : []<>(hr = h)

TypeAlwaysTrue == []HCini

THEOREM LSpec => TicksInfinitelyOften /\ EveryHourRecurs /\ TypeAlwaysTrue

SettlingProperty == <>[](hr = 1)

CounterexampleExists == 
    /\ hr = 1
    /\ [][HCnxt]_hr
    /\ <>~(hr = 1)

Init == HCini

Next == HCnxt

Spec == LSpec

=============================================================================