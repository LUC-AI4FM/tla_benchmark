---------------------------- MODULE NextStatePredicate ----------------------------
EXTENDS Integers

VARIABLES x

\* The predicate that constrains valid next-state values
\* Must be an even number in the range 0 through 9 (inclusive)
ValidNextValue(v) == v \in {0, 2, 4, 6, 8}

\* Initial state: variable starts at zero
Init == x = 0

\* Next state relation: the next value must satisfy the predicate
\* This is expressed purely as a constraint on x', with stuttering permitted
Next == x' \in {v \in Int : ValidNextValue(v)}

\* The complete specification allowing stuttering steps
Spec == Init /\ [][Next]_x

\* Type invariant implied by the state constraint
TypeInvariant == x \in Int

\* The constraint that should hold for all reachable states after any transition
\* (except the initial state which starts at 0, which happens to satisfy this anyway)
StateConstraint == ValidNextValue(x)

===================================================================================