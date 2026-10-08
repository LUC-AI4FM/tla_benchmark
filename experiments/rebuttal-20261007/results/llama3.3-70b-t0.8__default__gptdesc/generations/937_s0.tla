```
MODULE HourClockLiveness
EXTENDS Integers, HourClock
CONSTANTS
VARIABLES hr

Init == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == HCnxt

WF_hr == WF_vars(HCnxt, hr)

LSpec == HC \* WF_hr

TickingAlwaysHappens == <>[]<>HCnxt
EveryHourValueRecurs == \A i \in 1..12 : []<>hr = i
InitialConditionAlwaysTrue == []Init

THEOREM LSpec => (TickingAlwaysHappens /\ EveryHourValueRecurs /\ InitialConditionAlwaysTrue)

SettlingProperty == <>(hr = 5) 

Counterexample == 
  /\ hr = 1
  /\ [][Next]_hr
  /\ [](WF_hr)
```
Note: `HC` is assumed to be defined in the HourClock module, which this specification extends. If that's not the case and you need a complete definition for `HC`, it would look something like this:
```
HC == []<>HCnxt
```