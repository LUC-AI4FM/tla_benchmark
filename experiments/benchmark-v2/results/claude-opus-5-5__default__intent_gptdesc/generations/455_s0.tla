---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

Hours == 1..12

TypeInvariant == hr \in Hours

Init == hr \in Hours

Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: the counter always lies in 1..12
Safety == []TypeInvariant

\* Liveness: the counter keeps advancing forever (no infinite stuttering)
Progress == \A h \in Hours : []<>(hr = h)

AlwaysChanges == []<><<Next>>_vars

THEOREM Spec => Safety
THEOREM Spec => Progress
=============================================================================