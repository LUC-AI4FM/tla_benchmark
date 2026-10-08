----------------------------- MODULE ConsensusCore -----------------------------

EXTENDS Naturals, FiniteSets

(*
Core consensus decision problem:

- There is a set of processes Proc and a set of allowed values Values (both are CONSTANT parameters).
- Processes may propose values.
- At most once, one value becomes chosen.
- Processes may learn the chosen value.

Safety properties:
  1) Validity: any chosen value is in Values.
  2) Agreement: at most one distinct value can be chosen in any execution.
  3) Integrity: once a value is chosen it is never replaced by a different one.

Liveness (expressible under fairness):
  4) Eventual choice: under weak fairness of the Choose step and the assumption that
     proposals eventually persist, some value is eventually chosen.
  5) Nontriviality: if no value is ever proposed, then choosing nothing is a permitted outcome.
*)

CONSTANTS
  Proc,   \* Set of processes
  Values  \* Set of allowable values

VARIABLES
  proposed, \* Subset of Values that have been proposed by any process
  chosen,   \* Either {} (no value chosen) or {v} for some v \in Values
  learned   \* Map from process to what it has learned (either {} or {v})

vars == << proposed, chosen, learned >>

===============================================================================