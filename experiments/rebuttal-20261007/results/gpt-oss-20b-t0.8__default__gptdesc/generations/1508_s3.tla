MODULE SmallStateMachine
EXTENDS Naturals

VARIABLES x

MyNat == 0 .. 30

TypeOK == x \in MyNat

Init == x = 0

A ==
    /\ x' = IF x < 29 THEN x + 1 ELSE x

BandC ==
    /\ x' = IF x > 1 THEN x - 1 ELSE x

DandE ==
    /\ x' = x

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ [] (Next) /\ [](Inv)

END MODULE