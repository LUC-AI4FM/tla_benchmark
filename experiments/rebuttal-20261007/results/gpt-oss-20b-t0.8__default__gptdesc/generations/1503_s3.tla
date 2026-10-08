MODULE SmallSM

EXTENDS Naturals

VARIABLE x

Op(S, P, Q) == {s \in S : P(s) /\ Q(s, TRUE)}

Init ==
    x ∈ Op({1,2,3,4,5},
           \lambda s : s > 1,
           \lambda s,b : (s % 2 = 1))

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

===============================================================================