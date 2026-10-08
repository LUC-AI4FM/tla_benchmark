------------------------------ MODULE RandomFunctionSubset ------------------------------

EXTENDS Naturals, FiniteSets

(*
  This specification models an atomic, uniformly random selection of exactly K distinct
  total functions from Domain to Codomain as the initial state. In pure TLA+, probability
  is not represented; Init nondeterministically allows every K-sized subset of the function
  space, and the intended interpretation is that this initial choice is uniformly distributed
  over all such subsets. After initialization, the chosen subset is immutable.
*)

CONSTANTS
  Domain,    \* finite domain set
  Codomain,  \* finite codomain set
  N,         \* parameter: size of Domain
  M,         \* parameter: size of Codomain
  K          \* parameter: number of functions to select

(*
  Basic finiteness and sizing assumptions, and feasibility of selecting K functions.
*)
ASSUME Assumptions ==
  /\ IsFiniteSet(Domain)
  /\ IsFiniteSet(Codomain)
  /\ N \in Nat /\ M \in Nat /\ K \in Nat
  /\ N = Cardinality(Domain)
  /\ M = Cardinality(Codomain)
  /\ K <= Cardinality([Domain -> Codomain])

VARIABLES
  Chosen   \* the immutable K-sized subset of total functions Domain -> Codomain

(*
  Universe of all total functions from Domain to Codomain.
*)
FunSpace == [Domain -> Codomain]

(*
  All k-sized subsets of a set S.
*)
KSubsets(S, k) == { A \in SUBSET S : Cardinality(A) = k }

(*
  Initialization: atomically choose a K-sized subset of FunSpace.
*)
Init ==
  Chosen \in KSubsets(FunSpace, K)

(*
  No state changes after initialization.
*)
Next == UNCHANGED Chosen

Spec == Init /\ [][Next]_Chosen

(*
  Safety invariants about the chosen subset.
*)
TypeInv == Chosen \subseteq FunSpace
SizeInv == Cardinality(Chosen) = K

\* Redundant but explicit statement that no duplicates exist among elements of Chosen.
DistinctInv == \A f \in Chosen: Cardinality({ g \in Chosen : g = f }) = 1

(*
  Temporal safety: the chosen subset is always well-typed and of the correct size.
*)
Safety == [] (TypeInv /\ SizeInv)

(*
  Temporal immutability: after Init, Chosen never changes.
*)
Immutability == [][UNCHANGED Chosen]_Chosen

THEOREM Spec => Safety

=============================================================================