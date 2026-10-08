```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS S, P, Q
VARIABLES x

Op(S, P, Q) == {s \in S : P(s) /\ Q(s, TRUE)}

Init == x \in Op({1, 2, 3, 4, 5}, LAMBDA s : s > 1, LAMBDA s, t : s % 2 = 1)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x
```