---------------------------- MODULE TwelveHourClock ----------------------------
EXTENDS Integers

CONSTANTS Hours

ASSUME Hours = 1..12

VARIABLES hour

\* Type invariant: hour is always within valid range
TypeInvariant == hour \in Hours

\* Safety invariant: hour is always in range 1..12
SafetyInvariant == hour \in 1..12

\* Initial condition: hour starts as a valid 12-hour value
Init == hour \in Hours

\* Increment function with wrap-around from 12 to 1
Increment(h) == IF h = 12 THEN 1 ELSE h + 1

\* Transition relation: advance hour by exactly one, wrapping 12 to 1
Tick == hour' = Increment(hour)

\* Next state relation
Next == Tick

\* Functional correctness: each step advances hour by exactly one modulo 12
\* Expressed as: new hour equals (old hour mod 12) + 1
CorrectIncrement == [][hour' = (hour % 12) + 1]_hour

\* Alternative formulation of correct increment for action property
IncrementAction == hour' = (hour % 12) + 1

\* Specification with strong fairness to ensure infinite progress
Spec == Init /\ [][Next]_hour /\ SF_hour(Tick)

\* Liveness: the clock always eventually ticks (no deadlock)
AlwaysEventuallyTicks == []<><<Tick>>_hour

\* Liveness: every hour value is visited infinitely often
EventuallyHour(h) == []<>(hour = h)
AllHoursInfinitelyOften == \A h \in Hours : EventuallyHour(h)

\* Combined liveness property: clock cycles through all values infinitely
LivenessProperty == AllHoursInfinitelyOften

\* Deadlock freedom: from any state, a transition is always enabled
DeadlockFree == ENABLED Tick

\* Theorem: Spec implies the invariant holds globally
THEOREM Spec => []TypeInvariant

\* Theorem: Spec implies safety invariant holds globally  
THEOREM Spec => []SafetyInvariant

\* Theorem: Each transition preserves the invariant
THEOREM TypeInvariant /\ Tick => TypeInvariant'

\* Theorem: Step relation implements modulo-12 increment
THEOREM Spec => CorrectIncrement

\* Theorem: Under fair execution, all hours occur infinitely often
THEOREM Spec => AllHoursInfinitelyOften

================================================================================