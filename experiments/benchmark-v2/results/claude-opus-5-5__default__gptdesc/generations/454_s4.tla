------------------------------- MODULE TimerSpec -------------------------------
EXTENDS Reals

CONSTANT Rho

ASSUME RhoAssump == Rho \in Real /\ Rho > 0

-------------------------------- MODULE HourClock ------------------------------
EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC    == HCini /\ [][HCnxt]_hr
================================================================================