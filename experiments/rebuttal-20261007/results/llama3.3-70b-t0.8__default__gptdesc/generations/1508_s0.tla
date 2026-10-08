```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS MyNat

VARIABLES x

TypeOK == (x \in (0..30))

Init == (x = 0)

A == (x' = x + 1)

BandC == ((x > 10) => (x' = x - 1)) /\ ((x <= 10) => (x' = x + 2))

DandE == (x > 20) => (x' = 0)

Next == \/ A
          \/ BandC
          \/ DandE

Inv == TypeOK

Spec == Init /\ [][Next]_x

THEOREM Spec => []Inv
```