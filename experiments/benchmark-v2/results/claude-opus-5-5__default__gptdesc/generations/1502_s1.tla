---- MODULE OpStateMachine ----
EXTENDS Naturals

CONSTANT Op(_)

VARIABLE x

vars == << x >>

Init == x = 0

Next == x' \in Op(x)

\* Helper operators involving a subset expression
Subsets(S) == SUBSET S

ReachableSubsets == { T \in SUBSET Op(x) : x \in T \/ T = {} }

Spec == Init /\ [][Next]_vars

====