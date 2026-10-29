---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

TypeOK == hr \in 1..12

HCini == hr \in 1..12

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Init == HCini

Next == HCnxt

HC == HCini /\ [][HCnxt]_hr

Spec == Init /\ [][Next]_vars

HourInRange == hr \in 1..12

-----------------------------------------------------------------------------

THEOREM HC => []HCini

THEOREM Spec => []HourInRange

THEOREM Spec => []TypeOK

=============================================================================