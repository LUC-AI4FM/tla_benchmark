```
MODULE Sampler
EXTENDS Integers, FiniteSets
CONSTANTS S, T, RandomSubset
VARIABLE x

Init ==
  /\ S = {1, 2, 3, 4, 5, 6, 7, 8, 9}
  /\ T = 1..10
  /\ x \in RandomSubset(1000, [S -> T])

Next ==
  UNCHANGED x

Spec == Init /\ [][Next]_x

Inv == TRUE
```