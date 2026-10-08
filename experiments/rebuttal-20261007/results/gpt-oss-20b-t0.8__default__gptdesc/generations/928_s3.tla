MODULE HC2
EXTENDS HourClock

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

Spec == HC2

THEOREM HC_Equiv_HC2 : HC = HC2.