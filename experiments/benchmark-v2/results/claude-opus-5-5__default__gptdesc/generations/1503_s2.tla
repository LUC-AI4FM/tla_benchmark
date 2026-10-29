---------------------------- MODULE HigherOrderFilter ----------------------------
EXTENDS Naturals

VARIABLES x

vars == << x >>

\* Higher-order helper: filter S keeping elements s with P(s) and Q(s, TRUE)
Op(S, P(_), Q(_, _)) == { s \in S : P(s) /\ Q(s, TRUE) }

GreaterThanOne(s) == s > 1

IsOdd(s, b) == ((s % 2) = 1) = b

Filtered == Op({1, 2, 3, 4, 5}, GreaterThanOne, IsOdd)

Init == x \in Filtered

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

\* Safety invariants
TypeOK == x \in {1, 2, 3, 4, 5}

InFiltered == x \in Filtered

XGreaterThanOneAndOdd == x > 1 /\ (x % 2) = 1

=============================================================================