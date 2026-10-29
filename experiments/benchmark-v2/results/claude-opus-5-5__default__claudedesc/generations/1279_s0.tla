---- MODULE SingleVar ----
EXTENDS Integers

VARIABLES s

vars == <<s>>

Init == s = 23

Next(var) == \E val \in 0..1 : /\ val > 0
                               /\ var' = val

Spec == Init /\ [][Next(s)]_s

Inv == s # 0

TypeOK == s \in {1, 23}

THEOREM Spec => []Inv
====