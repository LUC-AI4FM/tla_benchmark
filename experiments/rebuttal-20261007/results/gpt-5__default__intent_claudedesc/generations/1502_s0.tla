------------------------------ MODULE HigherOrderOpDemo ------------------------------

EXTENDS Naturals

(*
This module demonstrates using a higher-order constant operator to drive state
transitions. The operator can be supplied/overridden in a model configuration.

- Gen(_) is a CONSTANT operator (arity 1). The Next-state relation picks x'
  nondeterministically from the set Gen(x).

- PowOfFixed(_) is a locally defined operator that ignores its argument and
  returns the powerset of a fixed finite set Fixed. A model can override Gen
  with PowOfFixed to instantiate the behavior without changing this module.

Example (informal) configuration override:
  CONSTANT
    Gen(_)
  DEFINITION
    Gen(v) == PowOfFixed(v)

or, equivalently:
  DEFINITION
    Gen(v) == SUBSET Fixed
*)

CONSTANTS Gen(_)

VARIABLES x

Fixed == {0, 1, 2}

PowOfFixed(v) == SUBSET Fixed

Init == x = 0

Next == x' \in Gen(x)

Spec == Init /\ [][Next]_x

=============================================================================