------------------------------ MODULE SmallSM ------------------------------
EXTENDS Naturals, Integers

VARIABLES x

MyNat == 0 .. 30

TypeOK == x \in MyNat

Init == x = 0

A ==
    /\ TypeOK
    /\ x' = (x + 1) % 31

BandC ==
    /\ TypeOK
    /\ x' = (x + 2) % 31

DandE ==
    /\ TypeOK
    /\ x' = (x + 3) % 31

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ [][Next]_x /\ [](Inv)

=============================================================================