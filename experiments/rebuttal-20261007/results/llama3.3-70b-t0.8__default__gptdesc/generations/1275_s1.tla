```
MODULE SingleVariableInitialization
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == \E x \in (0..1) : (s = x) /\ (x < 1)

Next == UNCHANGED s

Inv == s < 1

Spec == Init /\ [][Next]_s
```