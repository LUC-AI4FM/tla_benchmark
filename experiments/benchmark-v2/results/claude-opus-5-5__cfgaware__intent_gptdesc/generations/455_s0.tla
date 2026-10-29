---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

TypeOK == hr \in 1..12

HCini == hr \in 1..12

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

HCInv == hr \in 1..12

HCLiveSpec == HC /\ WF_hr(HCnxt)

HCProgress == \A k \in 1..12 : []<>(hr = k)

THEOREM HC => []HCInv
=============================================================================