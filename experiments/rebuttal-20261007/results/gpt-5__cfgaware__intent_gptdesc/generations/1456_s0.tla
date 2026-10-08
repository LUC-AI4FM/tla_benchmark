--------------------------- MODULE MutableSubset ---------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS

VARIABLES U, S, R

Universe == {1, 2, 3}

vars == << U, S, R >>

Init ==
  /\ U = Universe
  /\ S \subset U
  /\ R = [univ |-> U]

Next ==
  /\ U' = U
  /\ R' = R
  /\ S' \in SUBSET U

TypeOK ==
  /\ U = Universe
  /\ S \subseteq U
  /\ R = [univ |-> U]

Inv == TypeOK

(*
  State predicates useful for model checking:
  - Safety (subset is always within universe) is captured by TypeOK/Inv.
  - Universe invariance: U is always Universe; enforced by Next and captured in TypeOK/Inv.
  - Full set reached: S = U.
*)
FullSet == S = U
Safety == S \subseteq U

(*
  Action predicates useful for counting/classifying transitions:
  - UnchangedUniverse: universe and its record do not change during a step.
  - ElementGained(e): element e is added in this step.
  - ElementLost(e): element e is removed in this step.
*)
UnchangedUniverse ==
  /\ U' = U
  /\ R' = R

ElementGained(e) ==
  /\ e \notin S
  /\ e \in S'
  /\ UnchangedUniverse

ElementLost(e) ==
  /\ e \in S
  /\ e \notin S'
  /\ UnchangedUniverse

Spec == Init /\ [][Next]_vars

============================================================================