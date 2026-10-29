---------------------------- MODULE MC ----------------------------
(***************************************************************************)
(* Model-checking module for the ReadersWriters specification.            *)
(*                                                                         *)
(* Per the system description, this module adds exactly one top-level      *)
(* operator, n == 3. CONSTANTS, VARIABLES, Init, Next, Spec, the safety    *)
(* invariants, liveness properties and fairness conditions are inherited   *)
(* from ReadersWriters through EXTENDS. Defining any of them again here    *)
(* would cause a multiple-definition error in SANY.                        *)
(***************************************************************************)
EXTENDS ReadersWriters, TLC

n == 3

\* Notes on invariants violated during model checking.
\* These are comments only; this module defines no formulas for them.
\*
\* - Violated: an invariant asserting that no reader is ever active.
\*   The violation shows that the read path is reachable.
\* - Violated: an invariant asserting that no writer is ever active.
\*   The violation shows that the write path is reachable.
\* - Violated: an invariant asserting that the wait queue is always empty.
\*   The violation shows that actors can block and queue up.
\* - Violated: an invariant asserting that at most one reader is active.
\*   The violation shows that concurrent reads are possible.
\*
\* These are deliberately "falsified" sanity checks.
\* The real safety property inherited from ReadersWriters
\* (a writer excludes all other readers and writers) is expected to hold.

=============================================================================