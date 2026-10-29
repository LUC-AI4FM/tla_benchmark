---------------------------- MODULE PrimedParam ----------------------------
EXTENDS Naturals

VARIABLES s

vars == << s >>

Next(var) == \E i \in 0..1 : /\ var' = i
                              /\ var' > 0

Init == s = 23

Spec == Init /\ [][Next(s)]_s

Inv == s # 0

TypeOK == s \in Nat

THEOREM Spec => []Inv
=============================================================================