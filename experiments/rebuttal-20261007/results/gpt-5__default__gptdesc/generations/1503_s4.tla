------------------------------ MODULE SmallStateMachine ------------------------------

EXTENDS Integers

VARIABLES x

Op(S, P(_), Q(_, _)) ==
  { s \in S : P(s) /\ Q(s, TRUE) }

Init ==
  LET
    P1(s) == s > 1
    Q1(s, b) == (s % 2) = 1
  IN x \in Op({1, 2, 3, 4, 5}, P1, Q1)

Next ==
  UNCHANGED x

Spec ==
  Init /\ [][Next]_x

=============================================================================