---------------------------- MODULE Counter ----------------------------

EXTENDS Integers

VARIABLES counter

\* Type invariant: counter is always an integer between 1 and 5 inclusive
TypeInvariant == counter \in 1..5

\* Initial state: counter starts at 1
Init == counter = 1

\* Increment action: enabled when counter < 5, increments by exactly 1
Increment == 
    /\ counter < 5
    /\ counter' = counter + 1

\* Stutter action: when counter equals 5, it remains unchanged
Stutter ==
    /\ counter = 5
    /\ counter' = counter

\* Next-state relation: either increment or stutter
Next == Increment \/ Stutter

\* Fairness: weak fairness on Increment ensures enabled increments eventually occur
Fairness == WF_counter(Increment)

\* Complete specification with fairness
Spec == Init /\ [][Next]_counter /\ Fairness

------------------------------------------------------------------------
\* SAFETY PROPERTIES
------------------------------------------------------------------------

\* Bounds invariant: counter always stays between 1 and 5 inclusive
BoundsInvariant == counter >= 1 /\ counter <= 5

\* Monotonicity: counter never decreases (expressed as action property)
\* For any step, the new counter value is at least the old value
Monotonicity == [][counter' >= counter]_counter

\* Step constraint: counter never jumps by more than one
NoJump == [][counter' - counter <= 1]_counter

\* Combined safety: every step either increments by one or leaves unchanged
SafeStep == [][
    \/ (counter < 5 /\ counter' = counter + 1)
    \/ (counter = 5 /\ counter' = counter)
    \/ (counter' = counter)
]_counter

\* Main safety invariant combining all safety requirements
Safety == BoundsInvariant

------------------------------------------------------------------------
\* LIVENESS PROPERTIES
------------------------------------------------------------------------

\* Eventual stabilization: counter eventually reaches 5
EventuallyFive == <>(counter = 5)

\* Stability: once counter reaches 5, it stays at 5 forever
StableAtFive == [](counter = 5 => [](counter = 5))

\* Combined liveness: eventually reach 5 and stay there
EventualStabilization == <>[](counter = 5)

\* Main liveness property
Liveness == EventualStabilization

------------------------------------------------------------------------
\* AUXILIARY INVARIANTS
------------------------------------------------------------------------

\* Auxiliary invariant: counter is always positive
PositiveCounter == counter > 0

\* Auxiliary invariant: counter never exceeds 5
BoundedAbove == counter <= 5

\* Auxiliary invariant: counter is never below initial value
BoundedBelow == counter >= 1

\* Inductive invariant useful for proving properties
InductiveInvariant == counter \in 1..5

========================================================================