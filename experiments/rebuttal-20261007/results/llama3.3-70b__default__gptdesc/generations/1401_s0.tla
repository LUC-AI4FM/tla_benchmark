```
MODULE CounterSystem
EXTENDS Integers
CONSTANTS 
VARIABLES outerX

InnerModule(x) == 
  [*]x = x + 1 & x < 3

Fairness == WF_Vars(InnerModule(outerX))

Init == outerX = 0

Next == 
  /\ (InnerModule(outerX)) 
  \/ (UNCHANGED <<outerX>>)

Spec == Init /\ [][Next]_<<outerX>> /\ Fairness
Liveness == <> (outerX = 3)
THEOREM Spec => Liveness
```