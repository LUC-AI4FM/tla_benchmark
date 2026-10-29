---- MODULE PrimedParam ----
EXTENDS Integers

VARIABLE s

vars == <<s>>

Init == s = ""

Next(x) == \E v \in {0, 1} : x = v /\ x > 0

Spec == Init /\ [][Next(s')]_vars
====