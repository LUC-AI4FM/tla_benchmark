```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS S

VARIABLE x

Op(S, P, Q) == {s \in S : P(s) /\ Q(s, TRUE)}

Init == x \in Op({1, 2, 3, 4, 5}, lambda s : s > 1, lambda <<s, t>> : s % 2 = 1)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x
```