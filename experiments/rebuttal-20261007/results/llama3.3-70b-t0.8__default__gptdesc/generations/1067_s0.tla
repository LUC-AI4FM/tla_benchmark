```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS Node

VARIABLES active, detected

Init ==
  /\ active \in [Node -> {True, False}]
  /\ detected = False

Next ==
  (\E n \in Node :
    /\ active[n] = True
    /\ active' = [active EXCEPT ![n] = False]
    /\ detected' = detected
  )
  \/ (\E n \in Node :
    /\ active[n] = True
    /\ \E m \in Node :
      /\ m /= n
      /\ active[m] = False
      /\ active' = [active EXCEPT ![m] = True]
      /\ detected' = detected
  )
  \/ (detected' = True
    /\ detected = False
    /\ \A n \in Node : active[n] = False
    /\ active' = active
  )
  \/ (detected' = detected
    /\ active' = active
  )

Spec ==
  Init /\ [][Next]_active

TerminationDetected == detected = True
AllInactive == \A n \in Node : ~active[n]
Correctness == []<>(AllInactive => TerminationDetected)
Quiescence == <>[]~(\E n \in Node : active[n])
Liveness == SF_Var(detected)

THEOREM Spec => []Correctness
THEOREM Spec => Quiescence
THEOREM Spec => Liveness

Fairness ==
  WF_Var(<<n \in Node |-> TRUE>>_detected)
```
Note: This TLA+ module uses the `Integers` and `FiniteSets` modules from the standard TLA+ library. The `SF_Var` and `WF_Var` operators are used to specify fairness conditions on variables.