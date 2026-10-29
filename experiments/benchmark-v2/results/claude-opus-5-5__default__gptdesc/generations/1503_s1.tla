---------------------------- MODULE HigherOrderFilter ----------------------------
EXTENDS Naturals

VARIABLES x

vars == <<x>>

(* Higher-order helper: keep the elements s of S for which both P(s)  *)
(* and Q(s, TRUE) hold.                                               *)
Op(S, P(_), Q(_, _)) == { s \in S : P(s) /\ Q(s, TRUE) }

GreaterThanOne(s) == s > 1

IsOdd(s, b) == ((s % 2) = 1) = b

FilteredSet == Op({1, 2, 3, 4, 5}, GreaterThanOne, IsOdd)

Init == x \in FilteredSet

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

=============================================================================