----------------------------- MODULE SmallTemporalModel -----------------------------
EXTENDS Integers

VARIABLE s

Init == s = 23

Next(var) == ∃ v ∈ 0..1: /\ var' = v
                        /\ v > 0

Inv == s # 0

Spec == Init /\ []([Next(s)]_s)
================================================================================