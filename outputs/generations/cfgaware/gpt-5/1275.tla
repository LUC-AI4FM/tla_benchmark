---- MODULE InitPattern ----
EXTENDS Integers

VARIABLE s

Init(var) == \E v \in 0..1: var = v /\ var < 1

Spec == Init(s) /\ [] [UNCHANGED s]_s

Inv == s < 1

====