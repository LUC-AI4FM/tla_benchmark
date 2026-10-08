```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS S
VARIABLES x

Op(P, Q, S) == {s \in S : P(s) /\ Q(s, TRUE)}

Init == x \in Op(Lambda(s : s > 1), Lambda(s, t : s % 2 = 1), {1, 2, 3, 4, 5})

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

THEOREM Spec => []Init
```
Note: The `Lambda` operator in TLA+ is used to define anonymous functions. The first `Lambda` defines a function that takes an argument `s` and returns whether `s` is greater than 1, while the second `Lambda` defines a function that takes two arguments `s` and `t`, but only uses `s` to check if it's odd (since `t` must be `TRUE`). 

Also note that since there are no explicit liveness properties or fairness conditions mentioned in the description, this specification doesn't include them. The only safety invariant checked here is whether the initial condition holds forever (`THEOREM Spec => []Init`).