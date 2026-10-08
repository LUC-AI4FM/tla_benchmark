----------------------------- MODULE SingleValueConsensus -----------------------------

EXTENDS TLC

(*
  Minimal single-value consensus.
  - Deadlock checking should be disabled when model checking, since the system
    legitimately stutters forever after a choice is made.
*)

CONSTANT Values \* The fixed, candidate set of values.

VARIABLES Chosen

vars == << Chosen >>

Init ==
  /\ Chosen = {} \* Initially, nothing is chosen.

\* One-shot choice of a single value from the candidate set.
Choose(v) ==
  /\ Chosen = {}
  /\ v \in Values
  /\ Chosen' = {v}

\* The "some choice" action.
ChooseAny ==
  \E v \in Values: Choose(v)

\* Allow stuttering forever; after a choice, only stuttering remains possible.
Next ==
  ChooseAny \/ UNCHANGED Chosen

\* Base safety specification: no fairness.
Spec ==
  Init /\ [][Next]_vars

\* Fair variant: if choosing remains possible, it will eventually be taken.
SpecFair ==
  Init /\ [][Next]_vars /\ WF_vars(ChooseAny)

\* Safety invariants (validity, finiteness, agreement).
Validity ==
  Chosen \subseteq Values

FiniteChosen ==
  IsFiniteSet(Chosen)

Agreement ==
  Chosen = {} \/ \E v \in Values: Chosen = {v}

SafetyInv ==
  Validity /\ FiniteChosen /\ Agreement

\* Liveness (termination) property to be checked under SpecFair.
Termination ==
  <> (Chosen # {})

THEOREM TerminationUnderFairness ==
  SpecFair => Termination

=============================================================================