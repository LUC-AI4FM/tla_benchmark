---------------------------- MODULE spec ----------------------------

VARIABLE x

Op(S, P(_), Q(_, _)) == {s \in S : P(s) /\ Q(s, TRUE)}

GreaterThanOne(s) == s > 1

IsOdd(s, flag) == flag /\ (s % 2 = 1)

Init == x \in Op({1, 2, 3, 4, 5}, GreaterThanOne, IsOdd)

Next == UNCHANGED x

=========================================================================