---------------------------- MODULE specification ----------------------------

VARIABLE state

\* Initial condition: state starts as FALSE
Init == state = FALSE

\* First toggle action: flips the boolean value
Toggle1 == state' = ~state

\* Second toggle action: also flips the boolean value (equivalent but distinct action)
Toggle2 == state' = ~state

\* Next state relation: nondeterministically choose either toggle action
Next == Toggle1 \/ Toggle2

\* Type invariant: state is always a boolean
TypeInvariant == state \in BOOLEAN

\* Safety property: each transition flips the value (captured by the fact that
\* if we take a step, the new state is the negation of the old state)
FlipsValue == [][state' = ~state]_state

\* Safety property: state is always either FALSE or TRUE
AlwaysBoolean == state = FALSE \/ state = TRUE

\* The system does not converge to a fixed point - toggling always changes the value
\* This is captured by: whenever we take a non-stuttering step, state actually changes
NoFixedPoint == [][state' # state]_state

\* Liveness: the system can always make progress (never gets stuck)
\* From any state, Next is always enabled
AlwaysEnabled == []ENABLED(Next)

\* Fairness specification: weak fairness on both toggle actions
\* This ensures neither action is permanently ignored
Fairness == WF_state(Toggle1) /\ WF_state(Toggle2)

\* Complete specification with fairness
Spec == Init /\ [][Next]_state /\ Fairness

\* Liveness property: the system keeps toggling forever
\* Eventually state will be TRUE and eventually state will be FALSE, repeatedly
LivenessToggle == []<>state /\ []<>~state

\* Combined safety properties
Safety == TypeInvariant /\ AlwaysBoolean

=============================================================================