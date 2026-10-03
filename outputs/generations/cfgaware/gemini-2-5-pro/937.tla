---- MODULE LiveHourClock ----
EXTENDS Integers, TemporalLogic

VARIABLES hr

\* The initial condition: the hour is between 1 and 12.
HCini == hr \in 1..12

\* The next-state action: the hour advances by one, wrapping from 12 to 1.
HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

\* The base safety specification for the hour clock.
HC == HCini /\ [][HCnxt]_hr

\* The full liveness specification, requiring the clock to tick infinitely often.
LSpec == HC /\ WF_hr(HCnxt)

\* Property: The clock ticks infinitely often.
AlwaysTick == []<>HCnxt

\* Property: Every hour value from 1 to 12 is reached infinitely often.
AllTimes == \A h \in 1..12 : []<>(hr = h)

\* Property: The hour variable is always in its correct range.
TypeInvariance == [](hr \in 1..12)

\* A theorem stating that the liveness specification implies the desired properties.
THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance

\* A formula describing a behavior that violates LSpec by eventually settling
\* on a single value. This describes the structure of a counterexample to
\* a property like AlwaysTick when checked against the safety spec HC alone.
PostCondition == \E k \in 1..12 : <>(hr = k /\ [][hr' = hr]_hr)

=============================================================================