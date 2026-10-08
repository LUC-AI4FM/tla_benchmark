```
MODULE SingleVariableInitialization
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (Exists v \in 0..1 : s = v /\ s < 1)

Next == UNCHANGED s

Inv == s < 1

Spec == Init /\ [][Next]_s
```