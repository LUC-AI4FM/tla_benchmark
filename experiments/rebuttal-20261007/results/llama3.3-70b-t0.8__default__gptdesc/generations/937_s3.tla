```
MODULE HourClockLive
EXTENDS Integers, HourClock

CONSTANTS

VARIABLES hr

Init == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt

WF_hr == WF_vars(HCnxt, hr)

LSpec == HC \* WF_hr

TickingInfOften == <>[]<>HCnxt
HourRecursInfOften(i \in 1..12) == <>[]<>(hr = i)
InitTypingAlways == []Init

THEOREM LSpec => TickingInfOften /\ HourRecursInfOften(1) 
                  /\ ... /\ HourRecursInfOften(12) /\ InitTypingAlways

Postcondition == hr = 5
```