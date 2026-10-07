---- MODULE HourClock ----
EXTENDS Naturals

CONSTANT Twelve
ASSUME Twelve = 12

VARIABLES hr

HourSet == 1..Twelve

HCini == hr \in HourSet

HCnxt ==
  \/ /\ hr # Twelve
     /\ hr' = hr + 1
  \/ /\ hr = Twelve
     /\ hr' = 1

Init == HCini

Next == HCnxt

Spec == HCini /\ [][HCnxt]_hr

HC == Spec

THEOREM InvAlways == Spec => []HCini
====