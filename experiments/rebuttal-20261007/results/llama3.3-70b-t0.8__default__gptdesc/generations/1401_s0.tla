```
MODULE CounterSystem
EXTENDS Integers

CONSTANTS 

VARIABLES outerX

InnerModule(x) == 
  VARIABLES x
  Init == (x = 0)
  Step == (x < 3) /\ (x' = x + 1)
  Next == Step \/ (x' = x)
  Spec == Init /\ [][Next]_x
  Fairness == WF_vars(Step)

Init == outerX = 0

Next == InnerModule(outerX).Step \/ (outerX' = outerX)

Spec == Init /\ [][Next]_outerX

THEOREM Spec => []<(outerX = 3)> 
```