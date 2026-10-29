---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

Hours == 1..12

HCini == hr \in Hours

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr /\ WF_hr(HCnxt)

TypeOK == hr \in Hours

Inv == TypeOK

StepCorrect == [][hr' = (hr % 12) + 1]_hr

InvPreserved == [](hr \in Hours)

Progress == []<>(<<HCnxt>>_hr)

AllHoursRecur == \A h \in Hours : []<>(hr = h)

THEOREM HC => []TypeOK
THEOREM HC => StepCorrect
THEOREM HC => AllHoursRecur
====