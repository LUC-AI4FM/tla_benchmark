----------------------------- MODULE SingleVarSpec -----------------------------

EXTENDS Naturals

VARIABLES s

Next(var) ==
  ∃ v ∈ 0..1:
    /\ var' = v
    /\ v > 0

Init ==
  s = 23

Inv ==
  s # 0

Spec ==
  Init /\ [][Next(s)]_s

=============================================================================