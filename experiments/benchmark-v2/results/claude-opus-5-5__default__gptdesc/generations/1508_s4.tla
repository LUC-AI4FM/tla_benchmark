---- MODULE SmallStateMachine ----
EXTENDS Naturals

VARIABLE x

vars == x

MyNat == 0..30

TypeOK == x \in MyNat

Init == x = 0

Inv == TypeOK

A ==
    /\ x < 30
    /\ x' = x + 1

B ==
    /\ x < 29
    /\ x' = x + 2

C ==
    /\ x > 0
    /\ x' = x - 1

BandC == B \/ C

D ==
    /\ x % 2 = 0
    /\ x' \in MyNat

E ==
    /\ x' % 2 = 0
    /\ x' # x

DandE == D /\ E

Next == A \/ BandC \/ DandE

Spec == Inv /\ [][Next]_x

InitSpec == Init /\ [][Next]_x

THEOREM Spec => []TypeOK
====