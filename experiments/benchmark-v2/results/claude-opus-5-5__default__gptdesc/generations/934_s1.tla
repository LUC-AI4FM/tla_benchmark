---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

TypeOK == hr \in (1 .. 12)

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

Init == HCini

Next == HCnxt

HC == HCini /\ [][HCnxt]_hr

Spec == Init /\ [][Next]_vars

Invariant == HCini

THEOREM HC => []HCini
=============================================================================