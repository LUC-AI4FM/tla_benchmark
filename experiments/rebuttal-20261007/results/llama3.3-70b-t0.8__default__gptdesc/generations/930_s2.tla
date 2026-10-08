```
MODULE HourClock
EXTENDS Integers

CONSTANTS None

VARIABLES hr

HCini == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt

Init == HCini

Spec == Init /\ [][Next]_hr

THEOREM Spec => []HCini
```