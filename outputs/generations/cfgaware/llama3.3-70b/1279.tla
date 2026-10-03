```
MODULE SmallTemporalModel
VARIABLE s

Next(var) == 
  /\ var' \in 0..1
  /\ var' > 0

Inv == s /= 0

Init == s = 23

NextStep == [][Next(s)]_s

Spec == Init /\ [][NextStep]_s
```
Note: The `_s` subscript in `NextStep` and `Spec` indicates stuttering closure over the variable `s`. This allows the model to stutter (i.e., remain in the same state) at any step.