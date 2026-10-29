---- MODULE BoxedActionParam ----
EXTENDS Naturals

VARIABLE s

vars == << s >>

Next(var) == \E val \in 0..1 : var = val /\ var > 0

Init == s = ""

Spec == Init /\ [][Next(s')]_s

====