---------------------------- MODULE Toggle ----------------------------

VARIABLE state

\* Initial condition: state starts as TRUE
Init == state = TRUE

\* Transition relation: state flips to its logical negation
Flip == state' = ~state

\* Next state relation: either flip or stutter
Next == Flip \/ UNCHANGED state

\* Type invariant: state is always a boolean (safety)
TypeOK == state \in BOOLEAN

\* Strong invariant claim: state is always TRUE (this will NOT hold)
AlwaysTrue == state = TRUE

\* Weaker observational claim: state is a valid boolean value
ValidState == state = TRUE \/ state = FALSE

\* Safety: the state is always a boolean - no illegal values
Safety == []TypeOK

\* Liveness: system is not deadlocked - transitions always enabled
\* Either flip can occur or stuttering is allowed
NoDeadlock == [](ENABLED Flip \/ ENABLED (UNCHANGED state))

\* Liveness: the system can always make progress
Liveness == []<>(TRUE)

\* Property combining safety and liveness requirements
Prop == Safety /\ Liveness

\* Full temporal specification: initial condition with box-of-steps formula
Spec == Init /\ [][Next]_state

==========================================================================