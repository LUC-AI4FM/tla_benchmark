---------------------------- MODULE TwelveHourClock ----------------------------
EXTENDS Naturals

VARIABLES hour

TypeInvariant == hour \in 1..12

Init == hour \in 1..12

Tick == hour' = IF hour = 12 THEN 1 ELSE hour + 1

Next == Tick

Spec == Init /\ [][Next]_hour

ValidHour == hour \in 1..12

THEOREM Spec => []ValidHour

================================================================================