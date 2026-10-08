```
MODULE SingleVarInit
EXTENDS Integers, TLC

VARIABLE s

Init(v) == \E w \in 0..1 : (v = w /\ w < 1)

Next == UNCHANGED s

Spec == Init(s) /\ [] Next

Inv == s < 1
```