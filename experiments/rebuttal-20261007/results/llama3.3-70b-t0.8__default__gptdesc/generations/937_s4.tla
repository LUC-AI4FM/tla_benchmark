```
MODULE HourClockLive
EXTENDS HourClock
CONSTANTS H
VARIABLES hr

Init == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt

WF_hr == WF_vars(HCnxt, hr)

LSpec == HC \* WF_hr

Spec == Init /\ [][Next]_hr

THEOREM LSpec => []<>TICK
THEOREM LSpec => <>[]<>(hr = 1)
THEOREM LSpec => <>[]<>(hr = 2)
THEOREM LSpec => <>[]<>(hr = 3)
THEOREM LSpec => <>[]<>(hr = 4)
THEOREM LSpec => <>[]<>(hr = 5)
THEOREM LSpec => <>[]<>(hr = 6)
THEOREM LSpec => <>[]<>(hr = 7)
THEOREM LSpec => <>[]<>(hr = 8)
THEOREM LSpec => <>[]<>(hr = 9)
THEOREM LSpec => <>[]<>(hr = 10)
THEOREM LSpec => <>[]<>(hr = 11)
THEOREM LSpec => <>[]<>(hr = 12)

Postcondition == hr = 5
```