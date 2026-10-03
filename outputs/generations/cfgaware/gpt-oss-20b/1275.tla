------------------------------ MODULE SingleVarInit ------------------------------
EXTENDS Naturals

VARIABLE s

Init(var) == \E v \in 0..1 : (var = v /\ var < 1)

Spec == Init(s) /\ [] UNCHANGED s

Inv == s < 1

=============================================================================