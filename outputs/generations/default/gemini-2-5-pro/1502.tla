---- MODULE SimpleStateMachine ----
EXTENDS Naturals

CONSTANT Op

VARIABLE x

vars == <<x>>

\* Checks if a set S is a subset of the possible next values for x
IsSubsetOp(S) == S \subseteq Op(x)

\* An action where the next value of x is chosen from a given subset S
\* of the possible next values.
NextInSubset(S) == /\ S \subseteq Op(x)
                   /\ x' \in S

\* The initial state predicate.
Init == x = 0

\* The next-state relation.
Next == x' \in Op(x)

\* The temporal specification.
Spec == Init /\ [][Next]_vars

====================================