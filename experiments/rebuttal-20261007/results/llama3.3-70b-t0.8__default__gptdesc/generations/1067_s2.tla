```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

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

TerminationDetected == <>detected

Correctness == []<>(\A n \in Node : ~active[n]) => TerminationDetected

Quiescence == <<\A n \in Node : ~active[n]>>

Liveness == SF_VARIABLES detected

Fairness ==
  WF_VARIABLES (detected' = True) /\ [][Next]_<<active, detected>>

THEOREM Spec => []Correctness
THEOREM Spec => []Quiescence
THEOREM Spec => Liveness
THEOREM Spec => Fairness
```