```
MODULE SimpleSystemNeg
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init(var) == 
  \E x \in {0, 1} : var = x /\ x < 1

Init == Init(s)

Next == s' = s

Spec == Init /\ [][Next]_s

Inv == s < 1

THEOREM Spec => []Inv
```