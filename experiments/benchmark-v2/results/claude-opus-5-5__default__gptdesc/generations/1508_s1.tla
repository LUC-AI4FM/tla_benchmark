---- MODULE SmallStateMachine ----
EXTENDS Naturals

VARIABLES x

vars == << x >>

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

Inv == TypeOK /\ x = 0

A == /\ x < 30
     /\ x' = x + 1

B == /\ x % 2 = 0
     /\ x + 2 <= 30
     /\ x' = x + 2

C == /\ x % 2 = 1
     /\ x' = x - 1

BandC == B \/ C

D == x > 0

E == x' = x - 1

DandE == D /\ E

Next == A \/ BandC \/ DandE

Spec == Inv /\ [][Next]_x

THEOREM Spec => []TypeOK
====