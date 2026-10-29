------------------------------- MODULE MCBakery -------------------------------
(***************************************************************************)
(* Model-checking wrapper around the Bakery specification.                 *)
(*                                                                         *)
(* The bakery algorithm, its variables, Init, Next, Spec, and its safety   *)
(* invariants and liveness properties all come from module Bakery through  *)
(* EXTENDS. This module adds only a bounded replacement for Nat, so that   *)
(* ticket numbers stay in a finite range when the model is checked.        *)
(*                                                                         *)
(* To use it, put this substitution in the TLC configuration file:         *)
(*      CONSTANT Nat <- NatOverride                                        *)
(***************************************************************************)
EXTENDS Bakery, Naturals

CONSTANT MaxNat

ASSUME MaxNatAssumption == MaxNat \in Nat

NatOverride == 0 .. MaxNat

(***************************************************************************)
(* Init, Next, Spec, the invariants and the liveness properties are         *)
(* inherited unchanged from Bakery. Defining them again here would         *)
(* duplicate those definitions and cause a parse error.                    *)
(***************************************************************************)
================================================================================