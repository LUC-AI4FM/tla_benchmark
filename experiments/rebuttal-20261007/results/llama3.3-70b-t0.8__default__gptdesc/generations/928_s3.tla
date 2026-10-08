```
MODULE HC2
EXTENDS HourClock

CONSTANTS 

VARIABLES hr

Init == HCini

HCnxt2 == hr' = (hr % 12) + 1

Next == HCnxt2

Spec == Init /\ [][Next]_hr

THEOREM Spec => HC
```