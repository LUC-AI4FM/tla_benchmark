```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS MyNat

VARIABLES x

TypeOK == (x \in (0..30))

Init == (x = 0)

A == (x' = x + 1)

BandC == (x' = IF x < 10 THEN x + 2 ELSE x - 3)

DandE == (x' = IF x > 20 THEN x - 4 ELSE x + 5)

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ [][Next]_x
```