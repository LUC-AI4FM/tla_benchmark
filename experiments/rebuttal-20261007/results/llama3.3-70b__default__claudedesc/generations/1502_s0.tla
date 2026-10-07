```
MODULE MinimalSystem
EXTENDS Integers, FiniteSets
CONSTANTS Op
VARIABLES x

Id(n) == SUBSET {1, 2, 3}
Forty2 == Id

Init == x = {}

Next == x' \in Op(x)

Spec == Init /\ [][Next]_x

THEOREM Spec => []x \in SUBSET SUBSET {1, 2, 3}
```