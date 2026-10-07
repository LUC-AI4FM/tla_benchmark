----------------------------- MODULE SingleVarStateMachine -----------------------------

EXTENDS Integers

CONSTANTS MyNat
ASSUME MyNat = 0..30

VARIABLES x

TypeOK == x \in MyNat

Init == /\ x = 0
        /\ TypeOK

A == /\ x < 30
     /\ x' = x + 1

BandC == /\ x > 0
         /\ x' = x - 1

DandE == /\ x \in 5..30
         /\ x' = 0

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ []Inv /\ [][Next]_x

=======================================================================================