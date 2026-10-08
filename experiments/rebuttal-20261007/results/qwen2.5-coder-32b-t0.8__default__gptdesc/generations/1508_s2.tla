------------------------------- MODULE SmallStateMachine -------------------------------
EXTENDS Integers

CONSTANTS MyNat == 0..30

VARIABLES x

Init == x = 0

A == /\ x \in MyNat
     /\ x' = (x + 1) % 31

BandC == \/ /\ x \in MyNat
            /\ x' = x - 1
          \/ /\ x \in MyNat
            /\ x' = x * 2

DandE == \/ /\ x \in MyNat
            /\ x' = x / 2
          \/ /\ x \in MyNat
            /\ x' = (x + 2) % 31

Next == A \/ BandC \/ DandE

TypeOK == x \in MyNat

Inv == TypeOK

Spec == Init /\ [][Next]_<<x>>

====================================================================================