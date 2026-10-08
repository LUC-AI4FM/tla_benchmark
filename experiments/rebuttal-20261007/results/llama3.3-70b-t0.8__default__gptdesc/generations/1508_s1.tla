```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS MyNat

VARIABLES x

TypeOK == (x \in (0..30))

Init == (x = 0)

A == (x' = x + 1)
B == (x' = x - 1)
C == (x > 10) /\ (x' = x + 2)
D == (x < 20) /\ (x' = x * 2)
E == (x' = 0)

Next == (((A \/ B) /\ TypeOK') \/ C \/ D) \/ E

Inv == TypeOK

Spec == Init /\ [][Next]_x
```