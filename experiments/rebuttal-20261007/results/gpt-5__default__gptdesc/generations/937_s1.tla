------------------------------ MODULE LiveHourClock ------------------------------

EXTENDS Integers

CONSTANTS Dummy

VARIABLES hr

HCx == INSTANCE HourClock WITH hr <- hr

Init == HCx!HCInit
Next == HCx!HCnxt
HC   == HCx!HC

LSpec == HC /\ WF_hr(Next)

Spec == LSpec

TypeOK == hr \in 1..12
TypeAlways == []TypeOK

TickInfOften == []<>Next

AllHoursRecur == \A h \in 1..12: []<>(hr = h)

SettleToSomeHour == \E h \in 1..12: <>[](hr = h)

Post == AllHoursRecur /\ ~SettleToSomeHour

THEOREM Spec => TickInfOften /\ AllHoursRecur /\ TypeAlways

=============================================================================