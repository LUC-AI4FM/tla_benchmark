------------------------------- MODULE MC -------------------------------
EXTENDS ReadersWriters, TLC

\* Model value for the number of actors (readers/writers) in the system.
n == 3

\* Notes from model checking runs (comments only, not definitions):
\*   - Some candidate invariants were found to be violated, e.g. an
\*     invariant asserting that no reader is ever waiting while the
\*     resource is free, or that the waiting queue is always empty.
\*   - These are recorded here for reference only. The initial predicate,
\*     next-state relation, Spec, safety invariants, and liveness and
\*     fairness properties are all inherited from ReadersWriters.

=============================================================================