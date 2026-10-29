-------------------------------- MODULE ModCounter --------------------------------
(***************************************************************************)
(* A single counter process whose environment repeatedly increments the    *)
(* counter modulo a fixed positive bound.  The constant Bound is a global  *)
(* parameter, so other modules can instantiate this module with different  *)
(* values, for example:                                                    *)
(*     C1 == INSTANCE ModCounter WITH x <- y, Bound <- 3                   *)
(*     C2 == INSTANCE ModCounter WITH x <- z, Bound <- 7                   *)
(* The parameterised operators CInit, CNext and CSpec below support        *)
(* composing several counters inside a single module.                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Bound

ASSUME BoundAssumption == Bound \in Nat \ {0}

VARIABLE x

vars == <<x>>

---------------------------------------------------------------------------------
(* Initial-state predicates                                                     *)

\* Nondeterministic initialisation: any value in 0..Bound.
InitND == x \in 0..Bound

\* Deterministic initial assertion: states the range as explicit constraints.
InitAssert == /\ x \in Nat
              /\ 0 <= x
              /\ x <= Bound

Init == InitND

---------------------------------------------------------------------------------
(* Transition relation: one atomic increment step, reduced modulo Bound         *)

Inc == x' = (x + 1) % Bound

Next == Inc

\* Weak fairness of the process's atomic increment step.
Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------
(* Properties                                                                   *)

TypeOK == x \in 0..Bound

\* Safety: the counter stays within 0..Bound in every reachable state.
Safety == []TypeOK

\* Liveness: the value 0 recurs infinitely often.
Live == []<>(x = 0)

---------------------------------------------------------------------------------
(* Parameterised versions for modular instantiation and composition             *)

CInit(v, B) == v \in 0..B
CNext(v, B) == v' = (v + 1) % B
CSpec(v, B) == CInit(v, B) /\ [][CNext(v, B)]_v /\ WF_v(CNext(v, B))
CTypeOK(v, B) == v \in 0..B
CLive(v) == []<>(v = 0)

---------------------------------------------------------------------------------
(* Stated properties (proofs are not given)                                     *)

THEOREM InitConsistent == InitND => InitAssert

THEOREM SpecSafety == Spec => Safety

THEOREM SpecLiveness == Spec => Live

\* The same properties hold for an instance with any positive bound.
THEOREM GenericCounter ==
  ASSUME NEW B \in Nat \ {0},
         NEW VARIABLE v
  PROVE  CSpec(v, B) => ([]CTypeOK(v, B) /\ CLive(v))

\* Composition: two counters with different bounds, each with its own
\* proven properties, give the conjunction of those properties.
THEOREM Composition ==
  ASSUME NEW B1 \in Nat \ {0},
         NEW B2 \in Nat \ {0},
         NEW VARIABLE v,
         NEW VARIABLE w,
         CSpec(v, B1) => ([]CTypeOK(v, B1) /\ CLive(v)),
         CSpec(w, B2) => ([]CTypeOK(w, B2) /\ CLive(w))
  PROVE  (CSpec(v, B1) /\ CSpec(w, B2)) =>
            /\ [](CTypeOK(v, B1) /\ CTypeOK(w, B2))
            /\ CLive(v)
            /\ CLive(w)

=================================================================================