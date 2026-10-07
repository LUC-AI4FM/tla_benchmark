----------------------------- MODULE SmallMachine -----------------------------

EXTENDS Naturals

VARIABLES x

IsOdd(n) == \E k \in Nat: n = 2*k + 1

P(s) == s \in Nat /\ s > 1

Q(s, b) == b /\ IsOdd(s)

Op(S, P(_), Q(_, _)) ==
  { s \in S: P(s) /\ Q(s, TRUE) }

Init ==
  x \in Op({1, 2, 3, 4, 5}, P, Q)

Next ==
  UNCHANGED x

Spec ==
  Init /\ [][Next]_x

=============================================================================