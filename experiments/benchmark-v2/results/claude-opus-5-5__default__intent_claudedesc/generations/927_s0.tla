---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

TypeOK == hr \in 1..12

Init == hr \in 1..12

Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: the hour is always a valid 12-hour clock value
TypeInvariant == TypeOK

\* Progress: the clock can always advance to the next hour
CanAdvance == ENABLED Next

Progress == []CanAdvance

\* Cyclical behavior: after hour 12, the next tick yields hour 1
WrapAround == [][hr = 12 => hr' = 1]_vars

\* Each tick advances by exactly one hour, modulo 12
TickCorrect == [][hr' = IF hr = 12 THEN 1 ELSE hr + 1]_vars

\* Liveness: the clock keeps ticking, so every hour recurs infinitely often
EventuallyWraps == \A h \in 1..12 : []<>(hr = h)

THEOREM Spec => []TypeInvariant
THEOREM Spec => Progress
THEOREM Spec => WrapAround
THEOREM Spec => EventuallyWraps
====