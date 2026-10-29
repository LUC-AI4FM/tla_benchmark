---------------------------- MODULE HigherOrderFilter ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

(* Higher-order helper: filters S keeping elements s with P(s) and Q(s, TRUE) *)
Op(P(_), Q(_, _), S) == { s \in S : P(s) /\ Q(s, TRUE) }

GreaterThanOne(s) == s > 1

IsOddWhen(s, b) == b /\ (s % 2 = 1)

Filtered == Op(GreaterThanOne, IsOddWhen, {1, 2, 3, 4, 5})

FilteredLambda == Op(LAMBDA s : s > 1,
                     LAMBDA s, b : b /\ (s % 2 = 1),
                     {1, 2, 3, 4, 5})

Init == x \in Filtered

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

TypeOK == x \in {3, 5}

FilterConsistent == Filtered = FilteredLambda

InvX == x \in Filtered

=============================================================================