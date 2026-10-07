----------------------------- MODULE SingleVarInit -----------------------------
EXTENDS Integers

CONSTANTS Dummy

VARIABLES s

InitOp(x) ==
  \E v \in 0..1: x = v /\ x < 1

Init ==
  InitOp(s)

Next ==
  UNCHANGED s

Inv ==
  s < 1

Spec ==
  Init /\ [] [Next]_s

THEOREM Spec => []Inv
===============================================================================