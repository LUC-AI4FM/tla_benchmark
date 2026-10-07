```
MODULE F
EXTENDS Integers, TLC

CONSTANTS 

VARIABLES x

Op(S, P, Q) == {s \in S : P(s) /\ Q(s, TRUE)}

Init == x \in Op({1, 2, 3, 4, 5}, LAMBDA s : s > 1, LAMBDA s, b : (s % 2 # 0) /\ b)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x
```