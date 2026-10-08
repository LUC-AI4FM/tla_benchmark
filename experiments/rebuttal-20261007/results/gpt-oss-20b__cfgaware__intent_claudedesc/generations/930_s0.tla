------------------------------ MODULE Simple12HourClock ------------------------------
EXTENDS Naturals

CONSTANTS HC, HCini

VARIABLES hour

Init == (hour = HCini)

Next == (hour' = hour) \/ (hour' = IF hour = 12 THEN 1 ELSE hour + 1)

Spec == Init /\ [][Next]_hour

ValidHour == hour \in HC

THEOREM ClockInvariant: Spec => []ValidHour
=============================================================================