---- MODULE TemporalSubscript ----
EXTENDS Naturals

VARIABLES s

vars == << s >>

Init == s = ""

Next(var) == \E val \in 0..1 : var = val /\ var > 0

Spec == Init /\ [][Next(s')]_s

====