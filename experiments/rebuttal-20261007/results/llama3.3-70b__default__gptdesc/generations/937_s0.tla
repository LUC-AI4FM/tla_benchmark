```
MODULE HourClockLive
EXTENDS HourClock
CONSTANTS
VARIABLES hr

Init == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt

WF_hr == WF_vars(HCnxt, hr)

LSpec == HC /\ [][Next]_hr /\ WF_hr

THEOREM LSpec => <>[]HCnxt
THEOREM LSpec => \A i \in 1..12 : <>[]hr = i
THEOREM LSpec => []Init

Postcondition == <>(hr = 5 /\ hr' = 6)
```