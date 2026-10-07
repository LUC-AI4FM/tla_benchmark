```
MODULE H
EXTENDS Integers

CONSTANTS MyNat

VARIABLE x

Inv == (x \in MyNat) /\ (x = 0)

A == x' = 23

BandC == ((x \in MyNat) /\ (x' \in 23..25)) \/ (x < 25 /\ x' = 26)

DandE == (x = 23 /\ x' = 42) \/ (x = 123 /\ x' = 4711)

Next == A \/ BandC \/ DandE

Spec == Inv /\ [][Next]_x

THEOREM Spec => []Inv
```