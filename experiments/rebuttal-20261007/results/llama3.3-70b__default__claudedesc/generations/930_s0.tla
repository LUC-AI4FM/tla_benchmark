```
MODULE HourClock
EXTENDS Integers

CONSTANTS 

VARIABLES hr

HCini == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt ∨ (hr' = hr)

Spec == Init ∧ [][Next]_hr
Init == HCini

THEOREM Spec => []HCini
```