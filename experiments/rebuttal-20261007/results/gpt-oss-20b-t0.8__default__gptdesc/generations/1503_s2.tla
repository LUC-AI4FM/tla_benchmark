MODULE SmallSM
EXTENDS Integers

VARIABLE x

Op(S, P, Q) == { s \in S : P(s) /\ Q(s, TRUE) }

P1(s) == s > 1
Q1(s, b) == b /\ (s MOD 2 = 1)

Init == x ∈ Op({1,2,3,4,5}, P1, Q1)
Next == UNCHANGED x

Spec == Init /\ [] Next

===============================================================================