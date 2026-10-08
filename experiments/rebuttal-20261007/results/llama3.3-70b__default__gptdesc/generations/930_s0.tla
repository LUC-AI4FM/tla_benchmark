```
MODULE HourClock
EXTENDS Integers

CONSTANTS 

VARIABLES hr

Init == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt

Spec == Init /\ [][Next]_hr

THEOREM Spec => []Init
```