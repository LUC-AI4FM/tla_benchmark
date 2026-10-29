------------------------------- MODULE MCBoulanger -------------------------------
(***************************************************************************)
(* Model-checking wrapper around the Boulanger specification.              *)
(* Init, Next, Spec and all invariants and temporal properties come from   *)
(* the imported Boulanger module. This module adds only a bound on the     *)
(* natural numbers and a state constraint, so that the state space is      *)
(* finite.                                                                 *)
(***************************************************************************)
EXTENDS Boulanger

CONSTANT MaxNat

ASSUME MaxNat \in Nat

(***************************************************************************)
(* Bounded range of naturals, to be substituted for Nat in the model.      *)
(***************************************************************************)
NatOverride == 0 .. MaxNat

(***************************************************************************)
(* State constraint: every process's number stays below MaxNat.            *)
(***************************************************************************)
StateConstraint == \A process \in Procs : num[process] < MaxNat

=============================================================================