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
  /\ WF_<<active, detected>>(\E n \in Node : 
                              /\ detected' = True
                              /\ \A m \in Node : active[m] = False)

Correctness == [](\A n \in Node : ~active[n] => detected)
Quiescence == <>[]~(\E n \in Node : active[n])
Liveness == []<>(\A n \in Node : ~active[n])

THEOREM Spec => []Correctness
THEOREM Spec => Quiescence
THEOREM Spec => Liveness
```