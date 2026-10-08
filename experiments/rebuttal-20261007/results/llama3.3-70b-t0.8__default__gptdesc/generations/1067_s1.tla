```
MODULE TerminationDetection
EXTENDS Integers, TLC

CONSTANTS Node

VARIABLES active, detected

Init ==
  /\ active \in [Node -> {True, False}]
  /\ detected = False

Next ==
  \/ \E n \in Node :
      /\ active[n] = True
      /\ active' = [active EXCEPT ![n] = False]
      /\ detected' = detected
  \/ \E n \in Node :
      /\ active[n] = True
      /\ \E m \in Node : 
          /\ m /= n
          /\ active[m] = False
          /\ active' = [active EXCEPT ![m] = True]
          /\ detected' = detected
  \/ /\ detected' = True
     /\ \A n \in Node : active[n] = False
     /\ active' = active

Spec ==
  Init /\ [][Next]_<<active, detected>>
 WF_detection == <>(detected' = True)_

THEOREM Spec => []~(detected)_
THEOREM Spec => <>detected
THEOREM Spec => \A n \in Node : []<>(active[n] = False)
```
Note: `TLC` is used here to support the usage of `True` and `False`, if your TLA+ environment does not include it, consider using `BOOLEAN` instead.