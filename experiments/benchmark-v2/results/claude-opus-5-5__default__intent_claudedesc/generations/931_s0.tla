---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

TypeOK == hr \in 1..12

Init == hr \in 1..12

Next == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: the hour is always within 1..12
Safety == []TypeOK

\* Liveness: the clock never gets stuck on any hour forever
NeverStuck == \A h \in 1..12 : []<>(hr # h)

\* Liveness: every hour is reached infinitely often
AlwaysAdvances == \A h \in 1..12 : []<>(hr = h)

\* Liveness: from any hour, the next hour is eventually reached
Progress == \A h \in 1..12 : (hr = h) ~> (hr = IF h = 12 THEN 1 ELSE h + 1)

THEOREM Spec => Safety
THEOREM Spec => NeverStuck
THEOREM Spec => AlwaysAdvances
THEOREM Spec => Progress
====