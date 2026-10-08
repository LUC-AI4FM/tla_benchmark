--------------------------- MODULE HC2 ----------------------------
EXTENDS HourClock

HCnxt2 == hr' = (hr MOD 12) + 1

HC2 == HCini /\ [] [HCnxt2]_hr

Spec == HC2

THEOREM Equivalence == (Spec = HC)
=============================================================================