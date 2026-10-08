----------------------------- MODULE HourClockEquiv -----------------------------

EXTENDS Naturals, TLC, HourClock

CONSTANT Twelve
ASSUME Twelve = 12

VARIABLES hour

Init ==
  hour \in 1..Twelve

Next ==
  hour' = IF hour = Twelve THEN 1 ELSE hour + 1

ModNext ==
  hour' = (hour % Twelve) + 1

Spec ==
  Init /\ [][Next]_hour

ModSpec ==
  Init /\ [][ModNext]_hour

TypeInv ==
  hour \in 1..Twelve

Safety ==
  []TypeInv

THEOREM Spec => ModSpec

THEOREM ModSpec => Spec

THEOREM Spec <=> ModSpec

===============================================================================