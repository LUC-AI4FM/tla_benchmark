----------------------------- MODULE SimpleSingleVar -----------------------------

EXTENDS Integers

VARIABLES s

Init == s = 23

Next(var) ==
  ∃ val \in 0..1:
    /\ val > 0
    /\ var' = val

Inv == s # 0

Spec == Init /\ [][Next(s)]_s

THEOREM Spec => []Inv

=============================================================================