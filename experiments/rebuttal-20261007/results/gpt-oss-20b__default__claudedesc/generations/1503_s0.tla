MODULE F
EXTENDS Integers

VARIABLE x

Op(S, P, Q) ==
    { s \in S : P(s) /\ Q(s, TRUE) }

Init ==
    x \in Op({1,2,3,4,5},
             \lambda s: s > 1,
             \lambda s,b: (s % 2 ≠ 0) /\ b)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x