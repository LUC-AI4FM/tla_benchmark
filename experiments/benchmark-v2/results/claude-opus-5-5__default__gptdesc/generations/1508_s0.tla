---------------------------- MODULE SmallMachine ----------------------------
EXTENDS Naturals

VARIABLES x

vars == << x >>

MyNat == 0 .. 30

TypeOK == x \in MyNat

Init == x = 0

Inv == TypeOK

-----------------------------------------------------------------------------
(* Next-state actions *)

A == /\ x < 30
     /\ x' = x + 1

B == x' \in MyNat

C == x' # x

BandC == /\ x < 29
         /\ B
         /\ C
         /\ x' = x + 2

D == x > 0

E == x' = x - 1

DandE == /\ D
         /\ E

Next == A \/ BandC \/ DandE

-----------------------------------------------------------------------------
Spec == Inv /\ [][Next]_x

InitSpec == Init /\ [][Next]_x

THEOREM Spec => []TypeOK
THEOREM InitSpec => []Inv
=============================================================================