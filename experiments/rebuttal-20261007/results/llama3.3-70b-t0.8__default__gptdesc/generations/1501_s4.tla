```
MODULE SmallStateMachine
EXTENDS Naturals

CONSTANTS 

VARIABLES x

Init == (x = 0)

fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * fact[n-1]

A == (x' = fact[3])
B == (x' = fact[9])

Next == (A \/ B)

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
```