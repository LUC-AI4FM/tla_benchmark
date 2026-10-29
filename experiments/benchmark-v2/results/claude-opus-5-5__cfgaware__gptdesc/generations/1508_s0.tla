---- MODULE SmallStateMachine ----
EXTENDS Naturals

VARIABLE x

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

\* Basic increment action
A == /\ x < 30
     /\ x' = x + 1

\* B and C combined as alternatives
B == /\ x < 29
     /\ x' = x + 2

C == /\ x > 0
     /\ x' = x - 1

BandC == B \/ C

\* D and E combined as a conjunction of constraints on the step
D == /\ x >= 10
     /\ x' \in MyNat

E == /\ x' = x - 10

DandE == D /\ E

Next == A \/ BandC \/ DandE

\* State predicate used as the initial condition of Spec
Inv == Init /\ TypeOK

Spec == Inv /\ [][Next]_x

====