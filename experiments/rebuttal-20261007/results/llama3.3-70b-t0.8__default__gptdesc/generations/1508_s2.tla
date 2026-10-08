```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS MyNat

VARIABLES x

TypeOK == (x \in MyNat)

Init == (x = 0)

A == (x' = x + 1) /\
    (x < 30)

BandC == (x' = x - 1) /\ 
         (x > 0)

DandE == (x' = x) /\ 
        ((x = 0) \/ (x = 30))

Next == (A) \/ (BandC) \/ (DandE)

Inv == TypeOK

Spec == Init /\ [][Next]_x
```