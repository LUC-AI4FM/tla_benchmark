---- MODULE Skeleton ----
EXTENDS Naturals, TLC

VARIABLES x

vars == << x >>

\* Placeholder initial predicate: the description specifies no initial
\* condition, so x is left unconstrained.
Init == TRUE

\* Placeholder next-state relation: no algorithmic behavior is defined,
\* so every step is a stuttering step.
Next == UNCHANGED x

\* No fairness conditions are specified.
Spec == Init /\ [][Next]_vars

\* No invariants or liveness properties are described.
====