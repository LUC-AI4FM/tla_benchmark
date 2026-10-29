---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

TypeOK == hr \in 1..12

Init == hr \in 1..12

Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: the displayed hour is always between 1 and 12 inclusive
Safety == []TypeOK

\* Liveness: the clock always eventually advances (never stuck forever)
Progress == \A h \in 1..12 : [](hr = h => <>(hr # h))

Liveness == []<><<Next>>_vars

THEOREM Spec => Safety
THEOREM Spec => Progress
THEOREM Spec => Liveness
====