---------------------------- MODULE HC2 ----------------------------
EXTENDS Naturals

CONSTANT HCini

VARIABLE hr

HCnxt2 == hr' = (hr % 12) + 1

HC2 == HCini /\ [][HCnxt2]_hr

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr

THEOREM HC <=> HC2

=============================================================================