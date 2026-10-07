----------------------------- MODULE SingleVarInit -----------------------------
EXTENDS Integers

CONSTANTS DummyConst

VARIABLES s

Init(var) ==
  ∃ v ∈ 0..1:
    /\ var = v
    /\ v < 1

Next ==
  UNCHANGED s

Inv ==
  s < 1

Spec ==
  Init(s) /\ [] [Next]_s

THEOREM Spec => []Inv
=============================================================================