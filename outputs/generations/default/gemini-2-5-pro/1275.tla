---- MODULE SingleVariableInit ----
EXTENDS Integers

VARIABLES s

vars == <<s>>

Init(var) == \E val \in 0..1 : (var = val) /\ (val < 1)

Init == Init(s)

Next == UNCHANGED s

Spec == Init /\ [][UNCHANGED s]_s

Inv == s < 1

================================