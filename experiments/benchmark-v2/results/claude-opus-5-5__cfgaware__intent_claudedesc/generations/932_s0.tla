---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

TypeOK == hr \in 1..12

HCini == hr \in 1..12

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr

Spec == HC /\ WF_hr(HCnxt)

HCTypeInvariant == HCini

Progress == \A h \in 1..12 : [](hr = h => <>(hr # h))

Liveness == []<><<HCnxt>>_hr

-----------------------------------------------------------------------------
THEOREM Spec => []HCini
=============================================================================