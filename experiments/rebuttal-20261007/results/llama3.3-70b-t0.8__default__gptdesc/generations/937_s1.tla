```
MODULE HourClockLiveness
EXTENDS HourClock

CONSTANTS None

VARIABLES hr

Init == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt

WF_hr == WF_vars(HCnxt, hr)

LSpec == HC /\ WF_hr

Spec == Init /\ [][Next]_hr

THEOREM Spec => []<>HCnxt
THEOREM Spec => <>[]HCnxt
THEOREM Spec => \*[](hr \in 1..12)
THEOREM LSpec => Spec

Postcondition == <>[](hr = 12)
```