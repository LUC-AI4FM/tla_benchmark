------------------------------- MODULE InitAssignNeg -------------------------------

EXTENDS Integers

CONSTANTS Dummy

VARIABLES s

Init(var) ==
  \E v \in {0, 1}:
    /\ var = v
    /\ v < 1

Next ==
  UNCHANGED s

Spec ==
  Init(s) /\ [][Next]_s

Inv ==
  s < 1

=============================================================================