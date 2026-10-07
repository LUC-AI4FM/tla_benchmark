----------------------------- MODULE SmallMachine -----------------------------

EXTENDS Integers

CONSTANTS
  Dummy

VARIABLES
  x

Op(S, P(_), Q(_, _)) ==
  { s \in S : P(s) /\ Q(s, TRUE) }

GreaterThanOne(n) == n > 1

OddWithFlag(n, b) == (n % 2 = 1) /\ b

Init ==
  x \in Op({1,2,3,4,5}, GreaterThanOne, OddWithFlag)

Next ==
  UNCHANGED x

Spec ==
  Init /\ [][Next]_x

=============================================================================