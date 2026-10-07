```
MODULE HourClock2
EXTENDS HourClock
CONSTANTS 
VARIABLES hr

HCini == (hr \in 1..12)

HCnxt2 == hr' = ((hr % 12) + 1)

HC2 == HCini /\ [][HCnxt2]_hr

Spec == HC2

THEOREM HC <=> HC2
```