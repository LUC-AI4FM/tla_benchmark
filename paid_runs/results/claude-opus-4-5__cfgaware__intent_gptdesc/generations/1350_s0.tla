---------------------------- MODULE Counter ----------------------------

VARIABLE counter

\* Initial state: counter starts at 1
Init == counter = 1

\* Increment action: enabled when counter < 5, increments by exactly 1
Increment == /\ counter < 5
             /\ counter' = counter + 1

\* Stutter step when counter equals 5: counter remains unchanged
Stutter == /\ counter = 5
           /\ counter' = counter

\* Next state relation: either increment or stutter
Next == Increment \/ Stutter

\* Fairness: weak fairness on Increment ensures enabled increments eventually occur
Fairness == WF_counter(Increment)

\* Complete specification with fairness
Spec == Init /\ [][Next]_counter /\ Fairness

\* --------------------------------------------------------------------------
\* Auxiliary Invariants
\* --------------------------------------------------------------------------

\* The counter is always bounded between 1 and 5 inclusive
BoundedInvariant == counter \in 1..5

\* Type invariant
TypeOK == counter \in Int

\* --------------------------------------------------------------------------
\* Safety Properties
\* --------------------------------------------------------------------------

\* Safety: every step either increments by one (when below 5) or leaves unchanged
\* This is captured by the fact that Next only allows Increment or Stutter
\* and the step constraint [][Next]_counter

\* The counter never decreases (monotonicity)
Monotonic == [][counter' >= counter]_counter

\* The counter never jumps by more than one
NoJump == [][counter' <= counter + 1]_counter

\* Combined safety invariant
Safety == BoundedInvariant

\* --------------------------------------------------------------------------
\* Liveness Properties
\* --------------------------------------------------------------------------

\* Eventually the counter reaches 5
EventuallyFive == <>(counter = 5)

\* Once at 5, it stays at 5 forever (stability)
StableAtFive == [](counter = 5 => [](counter = 5))

\* The counter eventually reaches 5 and stays there forever
Liveness == EventuallyFive /\ StableAtFive

==========================================================================