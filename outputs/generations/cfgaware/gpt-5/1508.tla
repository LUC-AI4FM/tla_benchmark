---- MODULE SingleVarSM ----
EXTENDS Integers

VARIABLE x

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

A == /\ x < 30
     /\ x' = x + 1

BandC == /\ x > 0
         /\ x' = x - 1

DandE == /\ x <= 28
         /\ x' = x + 2

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ Inv /\ [] [Next]_x

====