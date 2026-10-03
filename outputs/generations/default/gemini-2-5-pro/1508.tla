---- MODULE SimpleStateMachine ----
EXTENDS Integers

MyNat == 0..30

VARIABLES x

TypeOK == x \in MyNat

Init == x = 0

A == /\ x < 30
     /\ x' = x + 1

BandC == \/ /\ x + 2 <= 30
            /\ x' = x + 2
         \/ /\ x + 3 <= 30
            /\ x' = x + 3

DandE == \/ /\ x + 4 <= 30
            /\ x' = x + 4
         \/ /\ x + 5 <= 30
            /\ x' = x + 5

Next == A \/ BandC \/ DandE

Inv == x \in MyNat

Spec == Init /\ [][Next]_x

================================