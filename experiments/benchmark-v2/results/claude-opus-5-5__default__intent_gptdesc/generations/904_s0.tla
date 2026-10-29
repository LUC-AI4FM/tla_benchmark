---- MODULE HourClock ----
EXTENDS Naturals

\* The fixed size of the clock cycle. This spec uses the 1..12 convention.
MaxHour == 12
Hours   == 1..MaxHour

VARIABLE hr

vars == <<hr>>

\* The hour that follows h on the cycle. Past the maximum it wraps to the minimum.
NextHour(h) == IF h = MaxHour THEN 1 ELSE h + 1

-----------------------------------------------------------------------------
\* Initial condition: the clock may start at any legal hour.
Init == hr \in Hours

\* The single external increment event: it advances the hour by one, with wrap-around.
Tick == hr' = NextHour(hr)

\* Allowed state transitions. Stuttering steps (hr' = hr) are allowed by [Next]_vars.
Next == Tick

\* Fairness assumption: Tick need not occur at every step, because stuttering is
\* permitted. However, Tick cannot be postponed forever while it is continuously
\* enabled. Tick is always enabled, so it occurs infinitely often.
Fairness == WF_vars(Tick)

\* Spec without fairness: any finite or infinite number of increments, mixed
\* with stuttering steps.
SafetySpec == Init /\ [][Next]_vars

\* Full spec, including the fairness assumption about the increment source.
Spec == SafetySpec /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* (1) Invariant: the hour is always within the allowed cyclic range.
TypeOK == hr \in Hours

\* (2a) Functional correctness of increment: every non-stuttering step moves
\*      to the successor hour on the cycle.
IncrementCorrect == [][hr' # hr => hr' = NextHour(hr)]_vars

\* (2b) Wrap-around: incrementing from the maximum produces the minimum.
WrapAround == [][(hr = MaxHour /\ hr' # hr) => hr' = 1]_vars

\* (2c) Without wrap-around, a non-wrapping increment adds exactly one.
NoWrapStep == [][(hr # MaxHour /\ hr' # hr) => hr' = hr + 1]_vars

-----------------------------------------------------------------------------
\* Liveness properties

\* The increment event happens infinitely often.
InfinitelyManyTicks == []<><<Tick>>_vars

\* (3) Recurrence: if increments occur infinitely often, then every hour of the
\*     cycle is visited infinitely often.
Recurrence == InfinitelyManyTicks => \A h \in Hours : []<>(hr = h)

\* Under the fairness assumption, recurrence holds unconditionally.
AlwaysEventuallyEveryHour == \A h \in Hours : []<>(hr = h)

\* The clock keeps making progress: from any hour, it eventually reaches the next hour.
Progress == \A h \in Hours : (hr = h) ~> (hr = NextHour(h))

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => IncrementCorrect /\ WrapAround /\ NoWrapStep
THEOREM Spec => Recurrence /\ AlwaysEventuallyEveryHour /\ Progress
THEOREM SafetySpec => Recurrence
=============================================================================