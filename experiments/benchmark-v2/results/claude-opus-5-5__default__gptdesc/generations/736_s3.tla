---------------------------- MODULE MCBakery ----------------------------
(***************************************************************************)
(* Model-checking wrapper around the Bakery specification.                *)
(* Init, Next, Spec, the safety invariants, the liveness properties and    *)
(* the fairness conditions all come from module Bakery through EXTENDS.    *)
(* Redefining them here would make SANY report multiple definitions.       *)
(* This module adds only a bounded override for the natural numbers, so    *)
(* that TLC can enumerate ticket values in a finite range.                 *)
(***************************************************************************)
EXTENDS Bakery, Naturals

CONSTANT MaxNat

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================