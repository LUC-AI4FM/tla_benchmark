----------------------------- MODULE HourClock -----------------------------
EXTENDS Naturals

CONSTANTS Twelve
ASSUME Twelve = 12

VARIABLES hr

HCini == hr \in 1..Twelve

HCnxt ==
  \/ /\ hr # Twelve
     /\ hr' = hr + 1
  \/ /\ hr = Twelve
     /\ hr' = 1

Init == HCini

Next == HCnxt

HC == Init /\ []Next

Spec == HC

THEOREM Spec => []HCini
============================================================================