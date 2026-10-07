----------------------------- MODULE SingleVarMachine -----------------------------
EXTENDS Integers

CONSTANTS MaxVal

ASSUME MaxVal = 30

VARIABLES x

MyNat == 0..MaxVal

TypeOK == x \in MyNat

Inv == TypeOK

Init == x = 0

A ==
  /\ x < MaxVal
  /\ x' = x + 1

BandC ==
  \/ /\ x <= MaxVal - 2
     /\ x' = x + 2
  \/ /\ x >= 2
     /\ x' = x - 2

DandE ==
  \/ /\ x # 0
     /\ x' = 0
  \/ /\ x = 0
     /\ x' = MaxVal

Next == A \/ BandC \/ DandE

Spec ==
  /\ Init
  /\ []Inv
  /\ [][Next]_x
============================================================================