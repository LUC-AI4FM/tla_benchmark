---- MODULE HourClock ----
EXTENDS Integers

VARIABLES hr

HCini == hr \in 1..12

HCnxt == IF hr = 12
           THEN hr' = 1
           ELSE hr' = hr + 1

HC == HCini /\ [][HCnxt]_hr

THEOREM HC => []HCini
========================