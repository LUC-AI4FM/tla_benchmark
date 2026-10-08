----------------------------- MODULE RandomFunctionSubset -----------------------------

EXTENDS Naturals, FiniteSets

(*
  Model of drawing a uniformly random fixed-size subset of a large finite function space.
  The selection occurs atomically in the initial state and is immutable thereafter.
*)

CONSTANTS
  N, \* size of the finite domain
  M, \* size of the finite codomain
  K  \* number of functions to select

(***************************************************************************)
(* Basic definitions                                                       *)
(***************************************************************************)

Domain == 1..N
Codomain == 1..M

FunSpace == [Domain -> Codomain]

KSubsets ==
  { S \in SUBSET FunSpace : Cardinality(S) = K }

(***************************************************************************)
(* Parameter well-formedness assumptions                                   *)
(***************************************************************************)

ASSUME
  /\ N \in Nat /\ N > 0
  /\ M \in Nat /\ M > 0
  /\ K \in Nat /\ K <= Cardinality(FunSpace)

(***************************************************************************)
(* State and dynamics                                                      *)
(***************************************************************************)

VARIABLES Chosen

vars == << Chosen >>

Init ==
  /\ Chosen \in KSubsets

Next ==
  UNCHANGED vars

Spec ==
  /\ Init
  /\ [] [Next]_vars

(***************************************************************************)
(* Invariants and properties                                               *)
(***************************************************************************)

TypeOK ==
  Chosen \subseteq FunSpace

SizeOK ==
  Cardinality(Chosen) = K

PairwiseDistinct ==
  \A f \in Chosen: \A g \in Chosen:
    f = g \/ \E x \in Domain: f[x] # g[x]

TotalityOK ==
  \A f \in Chosen:
    /\ DOMAIN f = Domain
    /\ \A x \in Domain: f[x] \in Codomain

Inv ==
  /\ TypeOK
  /\ SizeOK
  /\ PairwiseDistinct
  /\ TotalityOK

(*
  All steps are stuttering: the chosen subset never changes after initialization.
*)
Immutability ==
  [](UNCHANGED vars)

================================================================================