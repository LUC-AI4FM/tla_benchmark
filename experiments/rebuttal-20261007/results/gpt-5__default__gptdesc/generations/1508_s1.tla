--------------------------- MODULE SingleVarMachine ---------------------------

EXTENDS Naturals

CONSTANTS Max

ASSUME Max = 30

VARIABLES x

MyNat == 0..Max

TypeOK == x \in MyNat

Init == x = 0

A ==
  /\ x < Max
  /\ x' = x + 1

BandC ==
  /\ x \in MyNat
  /\ x' = x

DandE ==
  /\ x > 0
  /\ x' = x - 1

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ [][Next]_x /\ []Inv

=============================================================================