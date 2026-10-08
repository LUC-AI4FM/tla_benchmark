---- MODULE HourClock2 ----

CONSTANTS hr

VARIABLES \hr

HCini == 1 <= hr /\ hr <= 12

HCnxt2 == \/ hr' = (hr % 12) + 1
          \/ hr' = hr

HC == HCini /\ [][HCnxt]_\hr

HC2 == HCini /\ [][HCnxt2]_\hr

THEOREM HC => HC2

====