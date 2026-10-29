---- MODULE HigherOrderFilter ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Op(S, P(_), Q(_, _)) == { s \in S : P(s) /\ Q(s, TRUE) }

GreaterThanOne(n) == n > 1

IsOdd(n, b) == (n % 2 = 1) = b

Init == x \in Op({1, 2, 3, 4, 5}, GreaterThanOne, IsOdd)

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

TypeOK == x \in {3, 5}

====