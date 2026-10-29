---------------------------- MODULE HourClock2 ----------------------------
EXTENDS Naturals

VARIABLE hr

Hours == 1..12

HCini == hr \in Hours

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

HCinv == hr \in Hours

TypeOK == hr \in Hours

THEOREM HC2 => []HCinv

Wraparound ==
    /\ \A h \in 1..11 : (h % 12) + 1 = h + 1
    /\ (12 % 12) + 1 = 1

StepDeterministic ==
    \A h \in Hours : \E! n \in Hours : n = (h % 12) + 1

StepCorrect ==
    [][ /\ (hr = 12 => hr' = 1)
        /\ (hr \in 1..11 => hr' = hr + 1) ]_hr

LiveHC2 == HC2 /\ WF_hr(HCnxt2)

EveryHourInfinitelyOften == \A h \in Hours : []<>(hr = h)

THEOREM LiveHC2 => EveryHourInfinitelyOften

=============================================================================