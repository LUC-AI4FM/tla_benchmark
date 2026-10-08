------------------------------ MODULE SmallStateMachine ------------------------------
EXTENDS Integers

VARIABLE x

Op(S, P, Q) == { s \in S : P(s) /\ Q(s, TRUE) }

P(x) == x > 1
Q(x, b) == (b => (x % 2 = 1))

Init == x \in Op({1,2,3,4,5}, P, Q)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x
=============================================================================