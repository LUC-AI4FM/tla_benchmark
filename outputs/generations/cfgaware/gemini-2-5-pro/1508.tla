---- MODULE SimpleMachine ----
EXTENDS Integers

VARIABLES x

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

A == /\ x < 30
     /\ x' = x + 1

BandC == /\ x <= 25
         /\ x' = x + 5

DandE == /\ x > 10
         /\ x' = 0

Next == \/ A
        \/ BandC
        \/ DandE

Inv == x <= 15

Spec == Init /\ [][Next]_x

============================