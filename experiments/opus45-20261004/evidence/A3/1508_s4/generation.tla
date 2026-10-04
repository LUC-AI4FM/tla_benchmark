---------------------------- MODULE SmallStateMachine ----------------------------

EXTENDS Naturals

CONSTANTS MyNat

ASSUME MyNat = 0..30

VARIABLES x

TypeOK == x \in MyNat

Init == x = 0

A == x' = (x + 1) % 31

BandC == x' = (x + 2) % 31

DandE == x' = (x + 3) % 31

Next == A \/ BandC \/ DandE

Inv == x \in MyNat

Spec == Init /\ [][Next]_x /\ Inv

=============================================================================