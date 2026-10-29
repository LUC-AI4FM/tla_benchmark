---- MODULE NextParam ----
EXTENDS Integers

VARIABLE s

Next(var) == \E val \in {0, 1} : val > 0 /\ var' = val

Spec == s = 23 /\ [][Next(s)]_s

Inv == s # 0

====