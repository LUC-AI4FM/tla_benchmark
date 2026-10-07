-------------------------- MODULE SingleVarInit --------------------------

EXTENDS Integers

CONSTANTS R
VARIABLES s

ASSUME R = 0..1

Init(x) == \E v \in R: x = v /\ x < 1

Next == UNCHANGED s

Inv == s < 1

Spec == Init(s) /\ [] [UNCHANGED s]_s

=============================================================================