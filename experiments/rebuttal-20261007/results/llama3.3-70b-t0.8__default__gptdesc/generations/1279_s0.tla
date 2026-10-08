```
MODULE SmallTemporalModel
EXTENDS Integers

CONSTANTS

VARIABLES s

Init == (s = 23)

Next(var) == 
  /\ var' \in 0..1
  /\ var' > 0

NextAction == [][Next(s)]_s

Inv == s /= 0

Spec == Init /\ [][NextAction]_s

THEOREM Spec => []Inv
```