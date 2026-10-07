```
MODULE SimpleSystem
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (s = 23)

Next(var) == var' \in {0, 1} /\ var' > 0

Spec == Init /\ [][Next(s)]_s

Inv == s /= 0

THEOREM Spec => []Inv
```