---------------------------- MODULE test216c ----------------------------
EXTENDS Naturals

VARIABLE x

vars == <<x>>

InitC == x = 0

NextC == x' = (x + 1) % 6

SpecC == InitC /\ [][NextC]_x

Init == InitC
Next == NextC
Spec == SpecC

TypeOK == x \in Nat

RangeOK == x \in 0..5

THEOREM ThmC == SpecC => []TypeOK

THEOREM ThmC2 == [](x \in Nat)

THEOREM ThmC3 == 1 + 1 = 2

=============================================================================