```
MODULE CounterSystem
EXTENDS Integers
CONSTANTS 
VARIABLES outerX

InnerModule(x) == 
  /\ x = outerX
  /\ Step == (x < 3) /\ (x' = x + 1)
  /\ Fairness == WF_vars(Step)

Init == outerX = 0

Next == 
  /\ (InnerModule(outerX)) . Step 
  \/ ~(InnerModule(outerX)) . Step /\ outerX' = outerX

Spec == Init /\ [][Next]_<<outerX>>
THEOREM Spec => <> (outerX = 3)
```
Note: I added `THEOREM` to include the liveness property that `outerX` eventually reaches 3, as described in the system description.