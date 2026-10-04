---------------------------- MODULE specification ----------------------------

VARIABLES counter

\* Factorial results for the small constant (3) and large constant (9)
\* Factorial(3) = 6
\* Factorial(9) = 362880
SmallFactorialResult == 6
LargeFactorialResult == 362880

\* Set of valid counter values
ValidCounterValues == {0, SmallFactorialResult, LargeFactorialResult}

\* Set of factorial results that can be assigned
FactorialResults == {SmallFactorialResult, LargeFactorialResult}

\* Initial state: counter must be zero
Init == counter = 0

\* Short update: sets counter to factorial of small constant (3! = 6)
ShortUpdate == counter' = SmallFactorialResult

\* Long update: sets counter to factorial of larger constant (9! = 362880)
LongUpdate == counter' = LargeFactorialResult

\* Transition relation: nondeterministically choose either update
Next == ShortUpdate \/ LongUpdate

\* Type invariant: counter is always a valid value
TypeInvariant == counter \in ValidCounterValues

\* Safety property: after initialization, counter is always one of the factorial results
\* (initially it's 0, then it becomes one of the factorial values)
SafetyInvariant == counter \in ValidCounterValues

\* Safety property: every transition assigns exactly one factorial value
\* This is implicit in the definition of ShortUpdate and LongUpdate

\* The counter after any transition is a factorial result
CounterIsFactorialResult == counter \in FactorialResults

\* Liveness: the system does not deadlock (there is always some enabled transition)
\* Next is always enabled since ShortUpdate and LongUpdate have no preconditions
NoDeadlock == [][ENABLED Next]_counter

\* Fairness conditions allowing either update to occur indefinitely
\* Weak fairness ensures that if an action is continuously enabled, it eventually occurs
Fairness == WF_counter(ShortUpdate) /\ WF_counter(LongUpdate)

\* Overall behavior specification
Spec == Init /\ [][Next]_counter /\ Fairness

\* Liveness property: both updates can occur infinitely often
LivenessShort == []<><<ShortUpdate>>_counter
LivenessLong == []<><<LongUpdate>>_counter
Liveness == LivenessShort /\ LivenessLong

=============================================================================