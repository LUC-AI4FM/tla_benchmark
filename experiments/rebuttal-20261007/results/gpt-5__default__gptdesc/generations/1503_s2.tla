------------------------------- MODULE SmallStateMachine -------------------------------

EXTENDS Integers

CONSTANTS DummyConstant

VARIABLES x

Op(S, P(_), Q(_, _)) ==
  { s \in S : P(s) /\ Q(s, TRUE) }

Init ==
  LET P(s) == s > 1
      Q(u, t) == (u % 2) = 1
  IN x \in Op({1, 2, 3, 4, 5}, P, Q)

Next ==
  UNCHANGED x

Spec ==
  Init /\ [][Next]_x

=============================================================================