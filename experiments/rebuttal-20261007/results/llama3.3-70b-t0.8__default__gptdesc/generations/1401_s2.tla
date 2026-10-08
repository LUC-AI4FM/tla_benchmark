```
MODULE CounterSystem
EXTENDS Integers

CONSTANTS

VARIABLES outerX

InnerModule(x) == 
  VARIABLES x
  Init == (x = 0)
  Step == (x < 3) /\ (x' = x + 1)
  Fairness == WF_vars(Step)

Init ==
  outerX = 0

Next ==
  InnerModule(outerX).Step \/ (outerX' = outerX)

Spec ==
  Init /\ [][Next]_outerX
  /\ InnerModule(outerX).Fairness
  /\ <> (outerX = 3)
```