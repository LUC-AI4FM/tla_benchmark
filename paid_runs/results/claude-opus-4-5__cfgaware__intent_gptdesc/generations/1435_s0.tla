---------------------------- MODULE Specification ----------------------------

VARIABLE state

\* Initialization: state equals zero in the initial state
Init == state = 0

\* Next-state relation: state remains unchanged (stuttering only)
Next == state' = state

\* The complete specification with fairness allowing infinite stuttering
Spec == Init /\ [][Next]_state /\ WF_state(FALSE)

\* Initialization property: state equals zero initially
InitProperty == state = 0

\* Safety invariant: state equals zero in every reachable state
SafetyInvariant == state = 0

\* Liveness condition: always eventually the state equals zero
\* This is trivially satisfied since state never changes from zero
LivenessCondition == []<>(state = 0)

\* Type invariant for completeness
TypeInvariant == state \in Int

=============================================================================