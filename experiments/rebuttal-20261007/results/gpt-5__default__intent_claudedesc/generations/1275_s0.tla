----------------------------- MODULE NonTrivialInit -----------------------------
EXTENDS Integers

CONSTANTS UnusedConst

VARIABLES x

Init ==
  \E v \in 0..1 : v < 1 /\ x = v

Next ==
  UNCHANGED x

Spec ==
  Init /\ [][Next]_x

Inv ==
  x < 1

THEOREM Spec => []Inv
=============================================================================