---------------------------- MODULE InvariantAsSpec ----------------------------
EXTENDS Naturals

CONSTANT C

ASSUME C \in Nat

VARIABLE x

vars == <<x>>

TypeOK == x \in 0..3

Init == x = 0

SetConst    == x' = C
SetInRange  == x' \in 0..3
SetOutRange == x' = 10
Map1        == x = 1 /\ x' = 2
Map2        == x = 2 /\ x' = 0

Next == SetConst \/ SetInRange \/ SetOutRange \/ Map1 \/ Map2

Inv == TypeOK /\ x = 0

Spec == Init /\ [][Next]_vars /\ []Inv

FullSpec == Init /\ []Inv /\ [][Next]_vars

ClosedNext == [Next]_vars

Consistency == Init /\ Inv

THEOREM SpecConsistent == Spec => Init /\ []Inv /\ [][Next]_vars

THEOREM InitImpliesInv == Init => Inv
=============================================================================