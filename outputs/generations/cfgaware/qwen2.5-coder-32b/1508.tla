------------------------------- MODULE SmallStateMachine -------------------------------

CONSTANTS MyNat == 0..30

VARIABLES x

TypeOK == x \in MyNat

Init == x = 0

A == \/ x < 30 -> x' = x + 1
     \/ x = 30 -> x' = 0

BandC == \/ x > 0 -> x' = x - 1
         \/ x = 0 -> x' = 30

DandE == \/ x < 29 -> x' = x + 2
         \/ x >= 29 -> x' = (x + 2) % 31

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ [][Next]_<<x>>

=============================================================================