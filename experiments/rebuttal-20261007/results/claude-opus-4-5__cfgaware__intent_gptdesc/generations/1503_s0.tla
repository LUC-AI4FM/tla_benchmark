---------------------------- MODULE Specification ----------------------------

EXTENDS Integers

CONSTANTS 
    Universe,      \* The finite set of allowed integer values
    Threshold      \* The numeric threshold for the predicate

VARIABLES 
    state          \* The single value held by the system

\* The numeric predicate: value must be greater than the threshold
NumericPredicate(v) == v > Threshold

\* The Boolean requirement that must hold for the chosen value
\* This models an additional Boolean condition that depends on the element
BooleanRequirement(v) == v \in Universe /\ NumericPredicate(v)

\* The set of valid values satisfying both constraints
ValidValues == {v \in Universe : NumericPredicate(v) /\ BooleanRequirement(v)}

\* Type invariant: state is always in Universe
TypeOK == state \in Universe

\* Safety invariant: state satisfies both the numeric predicate and Boolean requirement
SafetyInvariant == 
    /\ state \in Universe
    /\ NumericPredicate(state)
    /\ BooleanRequirement(state)

\* Assumption that at least one valid value exists (initialization is satisfiable)
ASSUME ValidValues /= {}

\* Initial state: nondeterministically choose a value satisfying both constraints
Init == 
    /\ state \in ValidValues

\* Next state relation: no transitions change the state (stuttering only)
Next == 
    /\ UNCHANGED state

\* The complete specification
Spec == Init /\ [][Next]_state

\* Liveness property: the state persists forever once initialized
Liveness == []<>(state = state)

\* Full specification with fairness (trivial since Next only stutters)
FullSpec == Spec /\ WF_state(Next)

=============================================================================