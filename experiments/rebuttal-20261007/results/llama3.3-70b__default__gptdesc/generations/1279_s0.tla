```
MODULE SmallTemporalModel
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (s = 23)

Next(var) == 
  (\E x \in 0..1 : var' = x) /\ var' > 0

StutterStep == [][Next(s)]_s

Inv == s /= 0

Spec == Init /\ [][StutterStep]_s
```