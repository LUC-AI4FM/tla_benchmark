--------------------------- MODULE SingleVarInit ---------------------------

EXTENDS Integers

VARIABLES s

InitPred(var) == \E v \in 0..1 : var = v /\ var < 1

Init == InitPred(s)

Next == UNCHANGED s

Inv == s < 1

Spec == Init /\ [] [UNCHANGED s]_s

THEOREM Spec => []Inv

============================================================================