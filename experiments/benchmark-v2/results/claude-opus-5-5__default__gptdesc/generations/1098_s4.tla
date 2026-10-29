---------------------------- MODULE MCLamportMutex ----------------------------
(***************************************************************************)
(* Model-checking wrapper around the LamportMutex specification.           *)
(* Init, Next, Spec, and all invariants and liveness properties come from  *)
(* LamportMutex through EXTENDS, so they are not redefined here.           *)
(* NatOverride bounds the infinite set Nat for model checking. In TLC, use *)
(* it to override Nat (Nat <- NatOverride).                                *)
(***************************************************************************)
EXTENDS LamportMutex, Naturals

CONSTANT MaxNat

ASSUME MaxNatAssumption == MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================