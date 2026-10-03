---------------------------- MODULE LiveHourClock ----------------------------
EXTENDS Naturals

CONSTANT HCini

VARIABLE hr

TypeOK == hr \in (1..12)

HCini_def == hr \in (1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini_def /\ [][HCnxt]_hr

LSpec == HC /\ WF_hr(HCnxt)

Ticking == []<><<HCnxt>>_hr

HourRecurs(h) == []<>(hr = h)

AllHoursRecur == \A h \in (1..12) : HourRecurs(h)

AlwaysTypeOK == []TypeOK

THEOREM LSpec => Ticking /\ AllHoursRecur /\ AlwaysTypeOK

SettlingCounterexample == 
    /\ hr = 1
    /\ hr' = 2

Init == hr \in (1..12)

Next == HCnxt

Spec == Init /\ [][Next]_hr /\ WF_hr(Next)

=============================================================================