---------------------------- MODULE HourClock ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT MaxHour        \* intended value: 12

ASSUME MaxHourAssump == MaxHour = 12

VARIABLE hr

vars == <<hr>>

Hours == 1..MaxHour

\* Deterministic successor function for the hour
NextHour(h) == IF h = MaxHour THEN 1 ELSE h + 1

-----------------------------------------------------------------------------
\* Initial condition: the hour is any value in 1..12
Init == hr \in Hours

\* The only state change: a tick
Tick == hr' = IF hr = MaxHour THEN 1 ELSE hr + 1

Next == Tick

\* Weak fairness on Tick ensures ticks happen infinitely often
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Type / range invariant
TypeOK == hr \in Hours

\* Invariance as a temporal formula
AlwaysInRange == [](hr \in Hours)

\* Determinism of the tick step:
\* (a) state-level: from the current hour, exactly one successor hour
\*     satisfies the Tick relation
TickRel(h, h2) == h2 = IF h = MaxHour THEN 1 ELSE h + 1

DeterminismInv ==
    Cardinality({ h2 \in Hours : TickRel(hr, h2) }) = 1

\* (b) action-level: every step taken sets hr' to the unique NextHour(hr)
DeterministicStep == [][hr' = NextHour(hr)]_vars

Determinism == [](DeterminismInv) /\ DeterministicStep

\* No deadlock: a tick is always enabled
NoDeadlockInv == ENABLED Tick
NoDeadlock    == [](ENABLED Tick)

\* Progress: a tick always eventually occurs
Progress == []<><<Tick>>_vars

\* Cycle completeness: every hour in 1..12 is reached infinitely often
CycleCompleteness == \A h \in Hours : []<>(hr = h)

\* Reachability from any state: from any hour, every hour is eventually reached
EveryHourReachable == \A h \in Hours : <>(hr = h)

-----------------------------------------------------------------------------
THEOREM Spec => AlwaysInRange
THEOREM Spec => Determinism
THEOREM Spec => NoDeadlock
THEOREM Spec => Progress
THEOREM Spec => CycleCompleteness
THEOREM Spec => EveryHourReachable
=============================================================================