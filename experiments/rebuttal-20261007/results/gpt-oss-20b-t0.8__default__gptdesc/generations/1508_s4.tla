MODULE SmallMachine
EXTENDS Naturals

VARIABLE x

MyNat == 0 .. 30

TypeOK == x \in MyNat

Init == (x = 0) /\ TypeOK

A == /\ x' \in MyNat
    /\ IF x < 30 THEN x' = x + 1 ELSE x' = 0

BandC == /\ x' \in MyNat
       /\ IF x > 0 THEN x' = x - 1 ELSE x' = 0

DandE == /\ x' = x
       /\ x' \in MyNat

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ [] Inv /\ [][Next]_x