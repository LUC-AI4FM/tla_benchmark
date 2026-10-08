---------------------------- MODULE HourClock ----------------------------
EXTENDS Integers

VARIABLES Hour

INSTANCE HourClockBase WITH
  FH <- 1,
  LH <- 12,
  hr <- Hour

Init == HourClockBase!Init
Next == HourClockBase!Next
Tick == HourClockBase!Tick

Spec == Init /\ [][Next]_Hour /\ WF_Hour(Tick)

TypeOK == Hour \in 1..12
Safe == []TypeOK

InfTick == []<>(Tick)
AllHoursInf == \A h \in 1..12: []<>(Hour = h)

THEOREM LiveImpliesProps ==
  Spec => (InfTick /\ AllHoursInf /\ Safe)
=============================================================================