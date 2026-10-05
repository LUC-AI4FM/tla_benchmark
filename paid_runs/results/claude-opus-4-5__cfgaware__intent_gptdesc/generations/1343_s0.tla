---------------------------- MODULE specification ----------------------------

VARIABLES x, y

vars == <<x, y>>

\* Initial state predicate: both locations are zero
Init == x = 0 /\ y = 0

\* The only allowed transition is stuttering (no change)
\* This is expressed by allowing Next to be FALSE, meaning no non-stuttering steps
Next == FALSE

\* The complete specification with stuttering
Spec == Init /\ [][Next]_vars

\* Initial-state invariant: both locations are zero and equal
InitInvariant == x = 0 /\ y = 0

\* Invariant that values are equal
EqualityInvariant == x = y

\* Safety invariant: values remain equal (holds on all reachable states)
SafetyInvariant == x = y

\* Type invariant for the state space
TypeInvariant == x \in Int /\ y \in Int

\* Temporal property: initial condition holds at time 0
InitialConditionHolds == Init

\* Temporal property: values never change (always unchanged from initial state)
AlwaysUnchanged == [][UNCHANGED vars]_vars

\* Temporal property: equality holds forever
AlwaysEqual == []EqualityInvariant

\* Combined temporal property: init holds and all subsequent states maintain unchanged values
TemporalSpec == InitialConditionHolds /\ []UNCHANGED vars

\* Property expressing no divergence from initial equality
NoDivergence == [](x = y)

=============================================================================