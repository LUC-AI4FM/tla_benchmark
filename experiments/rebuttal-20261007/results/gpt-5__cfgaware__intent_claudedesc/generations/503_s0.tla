---- MODULE SingleValueConsensus ----
EXTENDS Naturals, FiniteSets

(*
  Minimal single-value consensus model.
  - A fixed set of candidate values: Values
  - A set of chosen values: Chosen (always size <= 1)
  - Initially: nothing chosen
  - At most once: one value may be chosen, then the system quiesces
  - Base Spec has no fairness; LiveSpec adds weak fairness so a choice
    is eventually made when enabled.

  Note: Model checking should disable deadlock checking because the system
  legitimately has no further non-stuttering steps after a choice is made.
*)

CONSTANT Values

VARIABLE Chosen

vars == << Chosen >>

Init ==
  Chosen = {}

Choose(v) ==
  /\ Chosen = {}
  /\ v \in Values
  /\ Chosen' = {v}

Choose ==
  \E v \in Values: Choose(v)

Next ==
  Choose

Spec ==
  Init /\ [][Next]_vars

LiveSpec ==
  Spec /\ WF_vars(Choose)

(*
  Safety invariant: "validity" and "agreement"
  - Chosen is a subset of Values
  - Chosen is finite
  - Chosen contains at most one element
*)
TypeOK ==
  Chosen \subseteq Values

Inv ==
  /\ TypeOK
  /\ IsFinite(Chosen)
  /\ Cardinality(Chosen) <= 1

(*
  Liveness (termination) property to be checked under LiveSpec:
  some value is eventually chosen.
*)
Termination ==
  <> (Chosen # {})

====