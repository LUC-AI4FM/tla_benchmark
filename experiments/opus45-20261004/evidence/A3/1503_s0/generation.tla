---------------------------- MODULE Spec ----------------------------

EXTENDS Integers

VARIABLES x

Op(S, P(_), Q(_, _)) == {s \in S : P(s) /\ Q(s, TRUE)}

GreaterThanOne(n) == n > 1

IsOdd(n, flag) == flag /\ (n % 2 = 1)

Init == x \in Op({1, 2, 3, 4, 5}, GreaterThanOne, IsOdd)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

=========================================================================