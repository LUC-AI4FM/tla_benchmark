```
MODULE HourClockLive
EXTENDS HourClock, TLC

CONSTANTS H

VARIABLES hr

Init == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

WF_hr == WF_vars({HCnxt}, {hr})

LSpec == HC /\ [][Next]_<<hr>> /\ WF_hr

Spec == LSpec

THEOREM Spec => <><>Ticking
THEOREM Spec => \A i \in 1..12 : <><>hr = i
THEOREM Spec => []Init

Postcondition == hr = 5 /\ HCnxt
```