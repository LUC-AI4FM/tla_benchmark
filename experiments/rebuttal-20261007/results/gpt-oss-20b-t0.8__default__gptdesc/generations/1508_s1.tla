MODULE SmallSM
EXTENDS Naturals

VARIABLE x

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

A == (x' = 0) /\ TypeOK

BandC == ((x' = x + 1 \/ x' = x - 1) /\ TypeOK)

DandE == (x' = x) /\ TypeOK

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ []Inv /\ [][Next]_x
