---------------------------- MODULE CounterMod6 ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

TypeOK == x \in Nat

InitC == x = 0

NextC == x' = (x + 1) % 6

Init == InitC

Next == NextC

SpecC == InitC /\ [][NextC]_x

Spec == SpecC

-----------------------------------------------------------------------------
(* Safety invariant: x is always a natural number *)
AlwaysNat == [](x \in Nat)

THEOREM SpecTypeOK == SpecC => [](x \in Nat)

THEOREM StandaloneAlwaysNat == [](x \in Nat)

THEOREM OnePlusOne == 1 + 1 = 2

=============================================================================