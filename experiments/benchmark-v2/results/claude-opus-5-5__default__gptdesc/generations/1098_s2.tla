---------------------------- MODULE MCLamportMutex ----------------------------
(***************************************************************************)
(* Model-checking wrapper around the existing LamportMutex specification.  *)
(*                                                                         *)
(* All state variables, Init, Next, Spec, the safety invariants (e.g.      *)
(* mutual exclusion and type correctness), the liveness properties and the *)
(* fairness conditions come from the extended LamportMutex module and are  *)
(* inherited unchanged. Redefining Init, Next or Spec here would clash     *)
(* with those inherited definitions.                                       *)
(*                                                                         *)
(* This module adds only a bounded substitute for Nat, so that TLC can     *)
(* enumerate the clock values.                                             *)
(***************************************************************************)
EXTENDS LamportMutex, Naturals

CONSTANT MaxNat

ASSUME MaxNat \in Nat

(***************************************************************************)
(* Bounded range used in the model to override Nat, e.g. Nat <- NatOverride*)
(***************************************************************************)
NatOverride == 0 .. MaxNat

=============================================================================