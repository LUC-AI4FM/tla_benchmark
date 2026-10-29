---- MODULE Spec ----
EXTENDS Naturals

VARIABLE s

Init == s = ""

Next(x) == \E v \in {0, 1} : x = v /\ x > 0

Spec == Init /\ [][Next(s')]_s
====