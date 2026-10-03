---------------------------- MODULE HourClock ----------------------------
VARIABLE hr

HCini == hr \in (1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr

THEOREM HC => []HCini

=============================================================================