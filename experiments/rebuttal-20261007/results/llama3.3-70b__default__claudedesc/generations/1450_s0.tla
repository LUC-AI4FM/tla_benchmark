```
MODULE RandomizationTest
EXTENDS Integers, Randomization
CONSTANTS S, T
VARIABLES x

Init == (x = RandomSubset(1000, [S -> T]))

Next == (x' = x)

Spec == Init /\ [][Next]_x

THEOREM Spec => []TRUE
```