----------------------------- MODULE SmallMachine -----------------------------
EXTENDS Integers

VARIABLES x

Op(S, P(_), Q(_,_)) == { s \in S : P(s) /\ Q(s, TRUE) }

P(s) == s > 1

Q(a, b) == b /\ (a % 2 = 1)

Init == x \in Op({1, 2, 3, 4, 5}, P, Q)

Next == UNCHANGED x
=============================================================================