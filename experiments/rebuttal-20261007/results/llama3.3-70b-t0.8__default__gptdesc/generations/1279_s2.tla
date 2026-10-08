```
MODULE SmallTemporalModel
EXTENDS Integers

CONSTANTS 

VARIABLES s

Init == (s = 23)

Next(var) == 
  EXISTS v \in 0..1 : 
    var' = v /\ var' > 0

StutterStep == 
  [][Next(s)]_s

Inv == s /= 0

Spec == Init /\ [][StutterStep]_s
```