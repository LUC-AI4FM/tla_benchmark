-------------------------------- MODULE H --------------------------------

EXTENDS Naturals

CONSTANT MyNat

VARIABLE x

A == x' = 23

BandC == \/ /\ x \in MyNat
            /\ x' \in 23..25
         \/ /\ x < 25
            /\ x' = 26

DandE == \/ /\ x = 23
            /\ x' = 42
         \/ /\ x = 123
            /\ x' = 4711

Next == A \/ BandC \/ DandE

Inv == x \in MyNat /\ x = 0

Spec == Inv /\ [][Next]_x

==========================================================================