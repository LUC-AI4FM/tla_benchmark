---- MODULE Skeleton ----
EXTENDS Naturals, TLC

VARIABLES x

vars == <<x>>

\* Placeholder initial predicate: no constraint on x is imposed.
Init == TRUE

\* Placeholder next-state relation: no algorithmic behavior; x stays unchanged.
Next == UNCHANGED x

\* Placeholder temporal specification: no fairness conditions.
Spec == Init /\ [][Next]_vars

====