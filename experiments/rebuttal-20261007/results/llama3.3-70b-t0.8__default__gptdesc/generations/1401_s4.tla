```
MODULE CounterSystem
EXTENDS Integers
CONSTANTS 
VARIABLES outerX

InnerModule(x) == 
  VARIABLES x
  Init == (x = 0)
  Step == (x < 3) && (x' = x + 1)
  Next == Step || (x' = x)
  Spec == Init /\ [][Next]_x
  Fairness == WF-vars(Step)

Init == outerX = 0

Next == 
  INNER.Step(outerX) || (outerX' = outerX)

Spec == 
  Init /\ [][Next]_outerX
  /\ InnerModule.Fairness(outerX)
  /\ <> (outerX = 3)

THEOREM Spec => []<> (outerX = 3)
```