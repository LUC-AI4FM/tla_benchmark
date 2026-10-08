```
MODULE SmallStateMachine
EXTENDS Integers
CONSTANTS MyNat
VARIABLES x

TypeOK == (x \in (0..30))

Init == (x = 0)

A == (x' = x + 1)
B == (x' = x - 1)
C == (x' = x)
D == (x' = x + 2)
E == (x' = x - 2)

Next == (((A \/ B) /\ x < 30) \/ ((C \/ D) /\ x >= 0) \/ (E /\ x > 0))

Inv == TypeOK

Spec == Init /\ [][Next]_x
```