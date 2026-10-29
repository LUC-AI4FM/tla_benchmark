---------------------------- MODULE MC ----------------------------
EXTENDS ReadersWriters, TLC

\* Model-checking configuration module for ReadersWriters.
\* Init, Next, Spec, the safety invariants and the liveness properties
\* (with their fairness conditions) are all inherited from ReadersWriters.
\* This module adds a single definition: n == 3.

n == 3

\* Notes on invariants observed to be violated while model checking.
\* These are comments only, not TLA+ definitions or formulas in this module:
\*   - A safety invariant (for example, mutual exclusion between readers
\*     and writers) may be violated under some configurations.
\*   - A type invariant may be violated if the queue or the set of actors
\*     grows beyond its expected bounds.
\*   - A liveness property may be violated when the required fairness
\*     conditions are not met.

====================================================================