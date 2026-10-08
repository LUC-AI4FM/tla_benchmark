------------------------------ MODULE SmallModel ------------------------------
EXTENDS Naturals, TLC

VARIABLE s

Init ==
  /\ s = 23

Next ==
  \E v ∈ 0..1 : (v > 0) /\ s' = v

Stutter ==
  s' = s

NextStutter == Next \/ Stutter

Inv ==
  s ≠ 0

Safety == [] Inv

Spec == Init /\ [][NextStutter]_s /\ Safety

=============================================================================