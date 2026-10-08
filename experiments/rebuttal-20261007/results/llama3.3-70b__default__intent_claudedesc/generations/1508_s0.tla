```
MODULE SimpleStateMachine
EXTENDS Integers

CONSTANTS MaxValue
VARIABLES x

Init == (x = 0)

Next == 
  \/ x' = 5
  \/ x' \in 1..3
  \/ x' = -1
  \/ (x = 2 /\ x' = 4)
  \/ (x = 3 /\ x' = 6)
  \/ x' = x

Spec == Init /\ [][Next]_x

THEOREM Spec => []Inv
Inv == x \in 0..0 /\ x = 0
```