----------------------------- MODULE SmallXMachine -----------------------------

EXTENDS Integers

CONSTANTS MyNat

ASSUME MyNat = 0..30

VARIABLES x

TypeOK == x \in MyNat

Inv == TypeOK

Init == x = 0

A == /\ x < 30
     /\ x' = x + 1

BandC ==
  \/ /\ x > 0
     /\ x' = x - 1
  \/ /\ x < 29
     /\ x' = x + 2

DandE ==
  \/ /\ x = 0
     /\ x' = 30
  \/ /\ x = 30
     /\ x' = 0

Next == A \/ BandC \/ DandE

Spec == /\ Init
        /\ Inv
        /\ [][Next]_x

Safety == []Inv

=============================================================================