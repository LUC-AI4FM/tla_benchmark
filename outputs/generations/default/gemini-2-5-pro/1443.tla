---- MODULE SimpleCounter ----
EXTENDS Integers, TLC

VARIABLES x

\* Helper predicate identifying when the state is 1.
IsOne == x = 1

\* Helper predicate identifying when all work is considered done.
Done == x = 2

\* Helper predicate identifying when the transition wraps from 2 back to 0.
Wraps == x = 2 /\ x' = 0

\* The initial state of the system.
Init == x = 0

\* The state machine advances x modulo 3 on each step.
Next == x' = (x + 1) % 3

\* The temporal specification of the system.
Spec == Init /\ [][Next]_x

\* A TLC-specific property that asserts the coverage of the named predicates.
\* For this finite model, TLC will explore all states and transitions.
\* This property checks that eventually the coverage counts stabilize to a
\* value of 1 for each of the three named predicates. This would typically be
\* checked by TLC by adding `CoverageAssertion` to the "Properties" section of the model.
CoverageAssertion ==
    LET cov == TLCGet("coverage")
    IN <>[](cov.IsOne = 1 /\ cov.Done = 1 /\ cov.Wraps = 1)

=============================================================================