----------------------------- MODULE SingleVarModel -----------------------------
EXTENDS Integers

CONSTANTS Dummy

VARIABLES s

Init ==
  s = 23

Next(x) ==
  ∃ v ∈ 0..1:
    /\ x' = v
    /\ v > 0

Inv ==
  s /= 0

Spec ==
  Init /\ [][Next(s)]_s
=============================================================================