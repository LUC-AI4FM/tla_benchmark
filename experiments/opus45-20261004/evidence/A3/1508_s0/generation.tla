---------------------------- MODULE SmallStateMachine ----------------------------
EXTENDS Naturals

CONSTANTS MyNat

VARIABLES x

TypeOK == x \in MyNat

Init == x = 0

A == x' = x + 1

BandC == x' = x + 2

DandE == x' = x + 3

Next == A \/ BandC \/ DandE

Inv == x \in MyNat

Spec == Init /\ [][Next]_x /\ Inv

=============================================================================