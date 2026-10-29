---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

TypeOK == hr \in 1..12

Init == hr \in 1..12

Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == Tick

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
====