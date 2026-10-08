```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES nodes, pending, detected

Init ==
  /\ nodes \in [1..N -> {active, inactive}]
  /\ pending \in [1..N -> Nat]
  /\ detected = FALSE

Next ==
  /\ (\/ i \in 1..N : nodes[i] = active)
    \/ (\/ i \in 1..N :
        /\ nodes[i] = inactive
        /\ pending[i] > 0)
    \/ (\/ i \in 1..N :
        /\ nodes[i] = active
        /\ nodes' = [nodes EXCEPT ![i] = inactive]
        /\ pending' = pending
        /\ detected' = detected)
    \/ (\/ i \in 1..N :
        /\ nodes[i] = active
        /\ pending[i] < N
        /\ pending' = [pending EXCEPT ![i] = @ + 1]
        /\ nodes' = nodes
        /\ detected' = detected)
    \/ (\/ i \in 1..N :
        /\ nodes[i] = inactive
        /\ pending[i] > 0
        /\ pending' = [pending EXCEPT ![i] = @ - 1]
        /\ nodes' = nodes
        /\ detected' = detected)
    \/ (\/ DetectTermination :
        /\ \A i \in 1..N : nodes[i] = inactive
        /\ \A i \in 1..N : pending[i] = 0
        /\ detected' = TRUE
        /\ nodes' = nodes
        /\ pending' = pending)

Spec ==
  /\ Init
  /\ [][Next]_nodes, pending, detected

TerminationImpliesDetection ==
  detected => (\A i \in 1..N : nodes[i] = inactive) /\ (\A i \in 1..N : pending[i] = 0)

StableTermination ==
  <<detected>>_detected

ActualTerminationLeadsToDetection ==
  <>(\A i \in 1..N : nodes[i] = inactive) /\ (\A i \in 1..N : pending[i] = 0)
    => <>detected

FairnessDetectTermination ==
  WF_DetectTermination(DetectTermination)

THEOREM Spec => []TerminationImpliesDetection
THEOREM Spec => StableTermination
THEOREM Spec => ActualTerminationLeadsToDetection
THEOREM Spec => FairnessDetectTermination
```
Note: This specification uses the `WF_DetectTermination` operator to specify weak fairness for the DetectTermination action. The `_nodes, pending, detected` subscript in the `Spec` definition indicates that these variables are state variables, which can be changed by actions.