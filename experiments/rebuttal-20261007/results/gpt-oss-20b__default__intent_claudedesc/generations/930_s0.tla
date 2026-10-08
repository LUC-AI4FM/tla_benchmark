MODULE TwelveHourClock
EXTENDS Integers

VARIABLE hour

vars == {hour}

Init == hour ∈ 1..12

Tick   == hour' = IF hour = 12 THEN 1 ELSE hour + 1
Stutter== hour' = hour

Next == Tick \/ Stutter

Spec == Init /\ [][Next]_vars

ValidHour == hour ∈ 1..12

THEOREM ClockInvariant == Spec => []ValidHour