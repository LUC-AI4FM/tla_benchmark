---- MODULE BoolFunSetToggle ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

\* The set of functions from {0} to {0}, filtered by the current value of x.
\* When x = TRUE, the set is {[i \in {0} |-> 0]} (non-empty);
\* when x = FALSE, the set is {} (empty).
FilteredSet == { f \in [{0} -> {0}] : x }

TypeOK == x \in BOOLEAN

Init == x = TRUE

Next == x' = (FilteredSet = {})

Spec == Init /\ [][Next]_vars

====