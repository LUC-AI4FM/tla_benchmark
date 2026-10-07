----------------------------- MODULE SingleVarInit -----------------------------
EXTENDS Integers

CONSTANTS DummyConst
VARIABLES s

InitOf(var) == ∃ v ∈ 0..1: var = v /\ v < 1

Init == InitOf(s)

Next == UNCHANGED s

Inv == s < 1

Spec == Init /\ [] [UNCHANGED s]_s
=============================================================================