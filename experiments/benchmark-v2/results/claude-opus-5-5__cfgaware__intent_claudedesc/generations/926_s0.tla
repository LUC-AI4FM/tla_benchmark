---------------------------- MODULE HourClock2 ----------------------------
EXTENDS Naturals

VARIABLE hr

HCini == hr \in (1 .. 12)

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

TypeOK == hr \in 1..12

THEOREM HC2 => []HCini
THEOREM HC2 <=> HC
=============================================================================