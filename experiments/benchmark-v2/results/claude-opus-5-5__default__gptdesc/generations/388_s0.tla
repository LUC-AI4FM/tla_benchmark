---------------------------- MODULE CounterModSix ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

Init == x = 0

NextC == x' = (x + 1) % 6

Next == NextC

Spec == Init /\ [][NextC]_x

TypeOK == x \in Nat

THEOREM SpecTypeOK == Spec => []TypeOK

THEOREM AlwaysNat == [](x \in Nat)

THEOREM OnePlusOne == 1 + 1 = 2

=============================================================================