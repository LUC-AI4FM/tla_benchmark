---------------------------- MODULE HourClock2 ----------------------------
EXTENDS Naturals

VARIABLE hr

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

THEOREM HC <=> HC2

=============================================================================