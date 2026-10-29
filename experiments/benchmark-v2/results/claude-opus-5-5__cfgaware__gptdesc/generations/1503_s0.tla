---- MODULE OpFilter ----
EXTENDS Naturals

VARIABLE x

vars == <<x>>

Op(S, P(_), Q(_, _)) == { s \in S : P(s) /\ Q(s, TRUE) }

Init == x \in Op({1, 2, 3, 4, 5},
                 LAMBDA s : s > 1,
                 LAMBDA s, b : b /\ (s % 2 = 1))

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars
====