---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr /\ WF_hr(HCnxt)

TypeOK == hr \in (1 .. 12)

Liveness == \A h \in (1 .. 12) : []<>(hr = h)

NeverStuck == \A h \in (1 .. 12) : (hr = h) ~> (hr # h)
--------------------------------------------------------------------------
THEOREM HC => []HCini
=============================================================================