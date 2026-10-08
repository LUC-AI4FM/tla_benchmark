-------------------------- MODULE HourClockLiveness --------------------------

EXTENDS Naturals

VARIABLE hr

HCInst == INSTANCE HourClock WITH hr <- hr

HCini == HCInst!HCini
HCnxt == HCInst!HCnxt
HC    == HCInst!HC

LSpec == HC /\ WF_hr(HCnxt)

AlwaysTick == []<><<HCnxt>>_hr

AllTimes == \A n \in 1..12 : []<>(hr = n)

TypeInvariance == []HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

=============================================================================