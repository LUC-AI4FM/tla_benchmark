---- MODULE Spec ----
EXTENDS Naturals

VARIABLE s

Next(var) == \E v \in 0..1 : var' = v /\ var' > 0

Spec == s = 23 /\ [][Next(s)]_s

Inv == s # 0
====