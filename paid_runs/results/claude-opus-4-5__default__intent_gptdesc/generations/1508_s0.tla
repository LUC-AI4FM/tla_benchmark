---------------------------- MODULE BoundedState ----------------------------

EXTENDS Naturals

CONSTANTS MinVal, MaxVal, InitialValue

VARIABLES state

\* The prescribed finite set of natural numbers (bounded numeric type)
BoundedDomain == MinVal..MaxVal

\* Type invariant: state variable remains within the bounded domain
TypeInvariant == state \in BoundedDomain

\* Initial condition: system starts with state set to InitialValue
Init == state = InitialValue

\* Transition 1: Unconditional assignment to a fixed value (MinVal)
AssignToMin == state' = MinVal

\* Transition 2: Unconditional assignment to another fixed value (MaxVal)
AssignToMax == state' = MaxVal

\* Transition 3: Next value lies in a contiguous subrange (middle portion of domain)
\* This allows nondeterministic choice within the subrange
AssignToSubrange == 
    LET lo == (MinVal + MaxVal) \div 3
        hi == (2 * (MinVal + MaxVal)) \div 3
    IN state' \in lo..hi

\* Transition 4: Guarded by current state being MinVal, enables increment
IncrementFromMin == 
    /\ state = MinVal
    /\ state' = state + 1

\* Transition 5: Guarded by current state being MaxVal, enables decrement
DecrementFromMax == 
    /\ state = MaxVal
    /\ state' = state - 1

\* Transition 6: Guarded by current state being in lower half, can jump to upper half
JumpToUpperHalf == 
    LET mid == (MinVal + MaxVal) \div 2
    IN /\ state \in MinVal..mid
       /\ state' \in (mid + 1)..MaxVal

\* Transition 7: Guarded by specific value (InitialValue), enables staying or moving by 1
FromInitialValue ==
    /\ state = InitialValue
    /\ state' \in {InitialValue, InitialValue + 1, InitialValue - 1}

\* Transition 8: Potentially contradictory with bounded type - tries to go beyond bounds
\* These transitions may produce values outside BoundedDomain
TryExceedUpperBound ==
    /\ state = MaxVal
    /\ state' = MaxVal + 1  \* This violates TypeInvariant if taken

TryExceedLowerBound ==
    /\ state = MinVal
    /\ state' = MinVal - 1  \* This violates TypeInvariant if taken (negative or below MinVal)

\* Transition 9: Unconditional assignment to a value that may be outside domain
AssignOutOfBounds == state' = MaxVal + 2  \* Potentially violates TypeInvariant

\* The complete next-state relation: disjunction of all allowed transitions
Next == 
    \/ AssignToMin
    \/ AssignToMax
    \/ AssignToSubrange
    \/ IncrementFromMin
    \/ DecrementFromMax
    \/ JumpToUpperHalf
    \/ FromInitialValue
    \/ TryExceedUpperBound
    \/ TryExceedLowerBound
    \/ AssignOutOfBounds

\* System specification with stuttering
Spec == Init /\ [][Next]_state

\* ----- Safety Properties to Verify -----

\* Safety Property 1: Type safety - state never leaves the prescribed finite domain
TypeSafety == TypeInvariant

\* Safety Property 2: Invariance of initial value combined with type correctness
\* This property asserts that state equals InitialValue AND is type-correct
\* (This will fail in reachable states where state != InitialValue)
InitialValueInvariant == state = InitialValue

\* Combined invariant: conjunction asserting type-correctness and initial value preservation
CombinedInvariant == TypeInvariant /\ InitialValueInvariant

\* ----- Assumptions for valid configuration -----
ASSUME MinVal \in Nat
ASSUME MaxVal \in Nat
ASSUME MinVal <= MaxVal
ASSUME InitialValue \in BoundedDomain

=============================================================================