---- MODULE HourClock12 ----
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

TypeOK == hr \in 1..12

Init == hr \in 1..12

\* Modular-arithmetic formulation of advancing the hour
HCnxt == hr' = (hr % 12) + 1

Next == HCnxt

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Alternative conditional (if-then-else) formulation
HCnxtAlt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

NextAlt == HCnxtAlt

SpecAlt == Init /\ [][NextAlt]_vars /\ WF_vars(NextAlt)

\* Safety: hour is always a valid 12-hour clock value
HourRangeInvariant == hr \in 1..12

\* Safety: proper cycling -- each step goes to the successor hour, wrapping 12 -> 1
ProperCycling == [][ (hr = 12 => hr' = 1) /\ (hr # 12 => hr' = hr + 1) ]_vars

\* The two formulations of the step relation agree on all valid hours
EquivalentSteps == \A h \in 1..12 : (h % 12) + 1 = IF h = 12 THEN 1 ELSE h + 1

\* Equivalence of the two specifications (as temporal properties)
SpecImpliesAlt == Spec => SpecAlt

\* Liveness: every hour is reached infinitely often
AllHoursVisited == \A h \in 1..12 : []<>(hr = h)

\* Liveness: after 12 the clock eventually returns to 1
WrapsAround == (hr = 12) ~> (hr = 1)

THEOREM Spec => []HourRangeInvariant
THEOREM Spec => ProperCycling
THEOREM EquivalentSteps
====