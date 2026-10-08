```
MODULE HigherOrderOperatorDemo
EXTENDS Integers, TLC

CONSTANTS

VARIABLES var

Init ==
  var = {x \in {1,2,3,4,5} : x > 1 /\ (x % 2 = 1) /\ TRUE}

Next ==
  UNCHANGED var

Spec ==
  Init /\ [][Next]_var

THEOREM Spec => []var = {2,4}
```