----------------------------- MODULE SmallMachine -----------------------------

EXTENDS Naturals

CONSTANT Op(_)

VARIABLES x

Init ==
  x = 0

Next ==
  x' \in Op(x)

Spec ==
  Init /\ [][Next]_x

SubsetOfOp(S, y) ==
  S \subseteq Op(y)

ProperSubsetOfOp(S, y) ==
  S \subset Op(y)

=============================================================================