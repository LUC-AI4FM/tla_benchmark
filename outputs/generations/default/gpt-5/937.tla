------------------------------ MODULE LiveHourClock ------------------------------

EXTENDS Naturals

CONSTANT Hours
ASSUME Hours = 12

VARIABLES hr

Init ==
  hr \in 1..Hours

HCnxt ==
  hr' = IF hr # Hours THEN hr + 1 ELSE 1

HC ==
  Init /\ [][HCnxt]_hr

Next ==
  HCnxt

LSpec ==
  HC /\ WF_hr(HCnxt)

Spec ==
  LSpec

TypeOK ==
  hr \in 1..Hours

AlwaysTypeOK ==
  []TypeOK

TicksInf ==
  []<>HCnxt

AllHoursInf ==
  \A h \in 1..Hours: []<>(hr = h)

SettleProp ==
  <>(\E h \in 1..Hours: [](hr = h))

NoSettle ==
  ~SettleProp

Post ==
  NoSettle /\ AllHoursInf /\ TicksInf

THEOREM LivenessAndRecurrenceFromLSpec ==
  LSpec => TicksInf /\ AllHoursInf /\ AlwaysTypeOK

===============================================================================