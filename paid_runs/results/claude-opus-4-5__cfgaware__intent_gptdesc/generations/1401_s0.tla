---------------------------- MODULE Specification ----------------------------

EXTENDS Naturals

VARIABLES observableValue

\* The subcomponent's local counter is exposed as the observable value
\* Initial state: observable value is 0
Init == observableValue = 0

\* Subcomponent increment action: increment counter from 0 up to 3
\* Only enabled when observableValue < 3
SubcomponentIncrement ==
    /\ observableValue < 3
    /\ observableValue' = observableValue + 1

\* Main controller stutter action: takes a step that leaves observable state unchanged
\* This is only taken when subcomponent is not enabled (i.e., observableValue >= 3)
MainControllerStutter ==
    /\ observableValue >= 3
    /\ UNCHANGED observableValue

\* Combined next-state relation: either subcomponent increments or main controller stutters
Next ==
    \/ SubcomponentIncrement
    \/ MainControllerStutter

\* Type invariant for safety
TypeInvariant == observableValue \in 0..3

\* Safety property: observable value is always in valid range
Safety == []TypeInvariant

\* Fairness constraint: weak fairness for subcomponent increment action
\* Ensures that when SubcomponentIncrement is continuously enabled, it eventually executes
Fairness == WF_observableValue(SubcomponentIncrement)

\* Complete specification with fairness
Spec ==
    /\ Init
    /\ [][Next]_observableValue
    /\ Fairness

\* Liveness goal: eventually the observable value reaches 3
Liveness == <>(observableValue = 3)

\* The property to be checked: under the specification (with fairness),
\* the eventual reachability of observable value 3 holds
Prop == Liveness

=============================================================================