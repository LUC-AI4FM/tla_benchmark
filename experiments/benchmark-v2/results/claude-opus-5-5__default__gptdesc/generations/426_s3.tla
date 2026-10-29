---------------------------- MODULE Placeholder ----------------------------
EXTENDS Naturals, TLC

VARIABLES x

vars == << x >>

\* The original module defines no concrete behavior. The definitions below
\* are trivial placeholders required for a well-formed specification. They
\* add no constraints and no transitions.

Init == TRUE

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

\* No safety invariants, liveness properties, or fairness conditions are
\* described for this module.
TypeOK == TRUE

=============================================================================