```
MODULE MinimalSystem

EXTENDS Integers, FiniteSets

CONSTANT Op
VARIABLE x

Id(n) == SUBSET {1, 2, 3}

Forty2 == Id

Init ==
  x = 0

Next ==
  x' \in Op(x)

THEOREM Spec == Init /\ [][Next]_x
```