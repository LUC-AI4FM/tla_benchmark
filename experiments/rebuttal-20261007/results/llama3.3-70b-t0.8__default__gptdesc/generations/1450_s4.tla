```
MODULE SingleVariableSystem
EXTENDS Integers, FiniteSets
CONSTANTS S, T, RandomSubset
VARIABLES x

Init == x \in RandomSubset(1000, [S -> T])

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

Inv == TRUE

THEOREM Spec => []Inv
```