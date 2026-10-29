---------------------------- MODULE CycleMod6 ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

InitC == x = 0

NextC == x' = (x + 1) % 6

Init == InitC

Next == NextC

SpecC == InitC /\ [][NextC]_x

Spec == SpecC

TypeOK == x \in Nat

InvRange == x \in 0..5

THEOREM SpecC => []TypeOK

THEOREM [](x \in Nat) => [](x \in Nat)

THEOREM 1 + 1 = 2

=============================================================================