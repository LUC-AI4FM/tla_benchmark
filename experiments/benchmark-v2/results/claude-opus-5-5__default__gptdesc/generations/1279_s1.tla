---- MODULE PrimedParam ----
EXTENDS Naturals

VARIABLE s

vars == << s >>

Next(var) == \E i \in 0..1 : var' = i /\ var' > 0

Init == s = 23

Spec == Init /\ [][Next(s)]_s

Inv == s # 0

THEOREM Spec => []Inv
====