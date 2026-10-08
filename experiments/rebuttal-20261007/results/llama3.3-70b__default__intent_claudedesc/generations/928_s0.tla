```
MODULE HourClockEquivalence
EXTENDS Integers, HourClock

CONSTANTS None

VARIABLES hour1, hour2

Init == (hour1 \in 1..12) /\ (hour2 = hour1)

Next1 == IF hour1 = 12 THEN hour1' = 1 ELSE hour1' = hour1 + 1
Next2 == hour2' = (hour2 + 1) % 12 + 1

Spec1 == Init /\ [][Next1]_hour1
Spec2 == Init /\ [][Next2]_hour2

THEOREM Spec1 => []Spec2
THEOREM Spec2 => []Spec1

ModelCheck == Spec1 => <>[]Spec2
```
Note: The `HourClock` module is assumed to be defined elsewhere, and its contents are not included in this specification.