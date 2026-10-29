---------------------------- MODULE MCBakery ----------------------------
(***************************************************************************)
(* A small wrapper around the Bakery specification. It introduces a       *)
(* bound MaxNat and defines NatOverride as the finite interval 0..MaxNat.  *)
(* NatOverride can stand in for the infinite set Nat when model checking,  *)
(* for example by substituting it in the TLC configuration with           *)
(* "Nat <- NatOverride". The algorithm, its initial predicate (Init), its *)
(* next-state relation (Next), its specification (Spec), and its safety    *)
(* and liveness properties are inherited from the extended Bakery module. *)
(***************************************************************************)
EXTENDS Bakery, Naturals

CONSTANT MaxNat

ASSUME MaxNatAssumption == MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================