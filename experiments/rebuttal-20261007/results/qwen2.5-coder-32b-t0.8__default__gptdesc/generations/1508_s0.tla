```tla
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS MyNat

VARIABLES x

Init == x = 0

TypeOK == /\ x \in MyNat

A == \/ x < 30 -> x' = x + 1
     \/ x = 30 -> x' = 0

BandC == \/ x > 0 -> x' = x - 1
        \/ x = 0 -> x' = 30

DandE == \/ x < 29 -> x' = x + 2
        \/ x >= 29 -> x' = x - 28

Next == A \/ BandC \/ DandE

Inv == TypeOK

Spec == Init /\ [][Next]_x /\ <>Invariant(Inv)
```