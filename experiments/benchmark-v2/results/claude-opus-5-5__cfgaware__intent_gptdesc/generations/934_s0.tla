---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

Hours == 1..12

NextHour(h) == IF h = 12 THEN 1 ELSE h + 1

HCini == hr \in Hours

HCnxt == hr' = NextHour(hr)

HC == HCini /\ [][HCnxt]_hr

FairHC == HC /\ WF_hr(HCnxt)

-----------------------------------------------------------------------------
TypeOK == hr \in Hours

Invariance == []HCini

DeterministicStep ==
    [][ \A h1, h2 \in Hours :
           (NextHour(hr) = h1 /\ NextHour(hr) = h2) => h1 = h2 ]_hr

TickFunctional == [][hr' = NextHour(hr)]_hr

CanTick == ENABLED HCnxt

NoDeadlock == []CanTick

AlwaysEventuallyTicks == []<><<HCnxt>>_hr

CycleComplete == \A h \in Hours : []<>(hr = h)

ReachEveryHour == \A h \in Hours : <>(hr = h)

THEOREM HC => []HCini
THEOREM FairHC => CycleComplete
=============================================================================