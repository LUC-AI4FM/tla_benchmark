MODULE SingleVarInit
EXTENDS Integers

VAR s

Init(var) == \E v \in 0..1 : var = v /\ var < 1

Next == UNCHANGED s

Spec == Init(s) /\ []Next

Inv == s < 1

END MODULE