---- MODULE TWELVE_HOUR_CLOCK ----
EXTENDS Integers

CONSTANTS MaxHour
ASSUME MaxHour = 12

VARIABLES hour

HourSet == 1..MaxHour

ValidHour == hour \in HourSet

Init == ValidHour

Tick ==
  \/ /\ hour < MaxHour
     /\ hour' = hour + 1
  \/ /\ hour = MaxHour
     /\ hour' = 1

Next == Tick

Spec == Init /\ [][Next]_hour

THEOREM ClockInvariant == Spec => []ValidHour

====