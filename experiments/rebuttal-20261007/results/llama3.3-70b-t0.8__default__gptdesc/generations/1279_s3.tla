```
MODULE SmallTemporalModel
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (s = 23)

Next(var) == 
  /\ var' \in 0..1
  /\ var' > 0

StutterStep == 
 [][Next(s)]_s

Spec == Init /\ [][StutterStep]_s

Inv == s /= 0

THEOREM Spec => []Inv
```