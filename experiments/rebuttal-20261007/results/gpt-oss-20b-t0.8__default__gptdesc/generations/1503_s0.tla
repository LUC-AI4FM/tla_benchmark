MODULE SmallSM
EXTENDS Naturals

Op(S, P, Q) == { s \in S : P(s) /\ Q(s, TRUE) }

P(s) == s > 1
Q(s, b) == b /\ (s % 2 = 1)

VARIABLE x

Init == x \in Op({1,2,3,4,5}, P, Q)

Next == UNCHANGED x

Spec == Init /\ [] Next