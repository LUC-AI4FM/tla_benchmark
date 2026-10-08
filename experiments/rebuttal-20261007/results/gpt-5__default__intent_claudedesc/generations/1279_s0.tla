------------------------------ MODULE GuardedChoice ------------------------------

EXTENDS Integers

CONSTANTS DUMMY

VARIABLES x

Init ==
  x = 23

Next ==
  /\ x' \in {0, 1}
  /\ x' > 0

Spec ==
  Init /\ [][Next]_x

(*
  Safety invariant: the variable never equals zero.
*)
NeverZero ==
  x # 0

AlwaysNeverZero ==
  [](x # 0)

=============================================================================