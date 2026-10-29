---------------------------- MODULE MC ----------------------------
EXTENDS ReadersWriters, TLC

n == 3

\* Violated invariants (noted for reference only; not defined here):
\*   - Invariant checks reported as violated during model checking of
\*     ReadersWriters with n == 3 are recorded in these comments only.
\*   - Init, Next, Spec, and all safety/liveness properties are
\*     inherited from the ReadersWriters module.

=============================================================================