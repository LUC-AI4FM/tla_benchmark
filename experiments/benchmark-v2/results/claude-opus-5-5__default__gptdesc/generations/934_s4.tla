---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

Init == HCini

Next == HCnxt

HC == HCini /\ [][HCnxt]_hr

Spec == HC

TypeInvariant == hr \in (1 .. 12)

-----------------------------------------------------------------------------

THEOREM HC => []HCini

=============================================================================