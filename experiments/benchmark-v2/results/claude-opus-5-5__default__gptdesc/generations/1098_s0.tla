---------------------------- MODULE MCLamportMutex ----------------------------
(***************************************************************************)
(* Wrapper around the LamportMutex specification for model checking.       *)
(* Init, Next, Spec, the safety invariants (e.g. Mutex), and any liveness  *)
(* properties and fairness conditions are inherited from LamportMutex.     *)
(* This module adds a bound MaxNat and NatOverride (0 .. MaxNat), which    *)
(* the model checker can substitute for Nat.                               *)
(***************************************************************************)
EXTENDS LamportMutex, Naturals

CONSTANT MaxNat

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================