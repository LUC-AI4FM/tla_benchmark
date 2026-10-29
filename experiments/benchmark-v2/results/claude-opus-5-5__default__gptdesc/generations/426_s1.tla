---------------------------- MODULE Skeleton ----------------------------
EXTENDS Naturals, TLC

\* No constants are declared in the original placeholder module.

VARIABLES x

vars == << x >>

\* The original skeleton defines no initial predicate. This is a trivial
\* placeholder that fixes x to an arbitrary natural value.
Init == x = 0

\* The original skeleton defines no transitions. This placeholder lets
\* the system only stutter.
Next == UNCHANGED x

\* No fairness conditions are described, so none are included.
Spec == Init /\ [][Next]_vars

\* No invariants or liveness properties are described. Only a trivial
\* type sanity check is provided.
TypeOK == x \in Nat

=============================================================================