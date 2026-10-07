----------------------------- MODULE SmallTemporalModel -----------------------------

EXTENDS Naturals

CONSTANTS Dummy

VARIABLES s

Init ==
  s = 23

Next(v) ==
  \E x \in 0..1:
    /\ v' = x
    /\ v' > 0

Spec ==
  Init /\ [][Next(s)]_s

Inv ==
  s # 0

=============================================================================