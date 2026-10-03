----------------------------- MODULE HigherOrderStutter -----------------------------
EXTENDS Integers

CONSTANTS Dummy

VARIABLES x

Op(S, P(_), Q(_, _)) ==
  { s \in S : P(s) /\ Q(s, TRUE) }

P(n) == n > 1

Q(n, b) == (n % 2) = 1 /\ b

Init == x \in Op({1, 2, 3, 4, 5}, P, Q)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x
================================================================================