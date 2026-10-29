---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

vars == <<hr>>

Hours == 1..12

TypeOK == hr \in Hours

Init == hr \in Hours

Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == Tick

Spec == Init /\ [][Next]_vars

\* Safety: the displayed hour is always between 1 and 12 inclusive
HourRangeInvariant == hr \in Hours

NeverInvalid == hr # 0 /\ hr # 13

\* Wraparound: a tick from hour 12 goes to hour 1
ProperWraparound == [][hr = 12 => hr' = 1]_vars

\* Each tick advances to the next hour cyclically
ProperAdvance == [][hr' = IF hr = 12 THEN 1 ELSE hr + 1]_vars

THEOREM Spec => []HourRangeInvariant
THEOREM Spec => []NeverInvalid
THEOREM Spec => ProperWraparound
THEOREM Spec => ProperAdvance
====