---------------------------- MODULE MCLamportMutex ----------------------------
(***************************************************************************)
(* Model-checking wrapper around the LamportMutex specification.           *)
(* Init, Next, Spec, the safety invariants and the liveness properties     *)
(* are all inherited from LamportMutex.                                     *)
(*                                                                         *)
(* This module adds a constant MaxNat and defines NatOverride as the       *)
(* finite range 0 .. MaxNat. A model can substitute NatOverride for Nat    *)
(* so that the state space is finite.                                       *)
(***************************************************************************)
EXTENDS LamportMutex

CONSTANT MaxNat

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================