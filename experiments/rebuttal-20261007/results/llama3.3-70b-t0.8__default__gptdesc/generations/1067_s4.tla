```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS Node

VARIABLES active, detected

Init ==
  /\ active \in [Node -> {True, False}]
  /\ detected = False

Next ==
  /\ (active' = active) \/ (\E n \in Node : 
      (* Termination *)
      /\ active[n] = True
      /\ active' = [active EXCEPT ![n] = False]
    )
  \/ (\E n \in Node, m \in Node :
      (* Wakeup *)
      /\ active[n] = True
      /\ active[m] = False
      /\ active' = [active EXCEPT ![m] = True]
    )
  \/ (* Detection *)
    /\ detected' = (active = [n \in Node |-> False])
    /\ detected = False
    /\ active' = active

Spec == Init /\ [][Next]_<<active, detected>>
  
Fairness == SF_VARIABLES (detected)

Correctness == []((\A n \in Node : ~active[n]) => detected)
Quiescence == <>[](~(\E n \in Node : active[n]))
Liveness == Correctness /\ Quiescence

THEOREM Spec => []Correctness
THEOREM Spec => []Quiescence
THEOREM Spec => Liveness
```