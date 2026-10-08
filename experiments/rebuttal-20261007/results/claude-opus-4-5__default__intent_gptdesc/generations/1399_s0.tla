---------------------------- MODULE BooleanToggle ----------------------------
EXTENDS Booleans

VARIABLES state

\* Type invariant - safety property that state is always a boolean
TypeInvariant == state \in BOOLEAN

\* Strong invariant claim - state is always true (this will NOT hold after a flip)
AlwaysTrue == state = TRUE

\* Weaker observational claim - state is either true or false (trivially true for booleans)
ValidState == state = TRUE \/ state = FALSE

\* Safety invariant - no illegal values appear
SafetyInvariant == TypeInvariant /\ ValidState

\* Initial condition - state starts as true
Init == state = TRUE

\* Flip action - state changes to its logical negation
Flip == state' = ~state

\* Stuttering action - state remains unchanged
Stutter == state' = state

\* Next state relation - either flip or stutter
Next == Flip \/ Stutter

\* Liveness: transitions are always enabled (flip or stutter is always possible)
TransitionsEnabled == ENABLED Flip \/ ENABLED Stutter

\* Deadlock freedom - there is always a valid next step
NoDeadlock == [][Next]_state => <>TRUE

\* The full temporal specification
Spec == Init /\ [][Next]_state

\* Liveness property: the system can always make progress (flip is always enabled)
FlipAlwaysEnabled == []ENABLED Flip

\* Liveness property: eventually the state can change
EventuallyCanFlip == <>ENABLED Flip

\* Combined safety properties for model checking
Safety == TypeInvariant /\ ValidState

\* Temporal property: type invariant holds throughout execution
TypeSafe == []TypeInvariant

\* Temporal property: valid state holds throughout execution  
AlwaysValidState == []ValidState

\* Temporal property: strong claim that state is always true (expected to fail)
StrongClaim == []AlwaysTrue

\* Temporal property: weaker claim that state remains boolean (expected to hold)
WeakClaim == []ValidState

===============================================================================