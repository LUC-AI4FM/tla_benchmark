```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES nodes, pending, terminated, detected

Init ==
  /\ nodes = [i \in 1..N |-> <<TRUE, 0>>]
  /\ pending = [i \in 1..N |-> 0]
  /\ terminated = FALSE
  /\ detected = FALSE

Next ==
  \/ \E i \in 1..N :
    /\ nodes[i] = <<TRUE, pending[i]>>
    /\ nodes' = [nodes EXCEPT ![i] = <<FALSE, pending[i]>>]
    /\ pending' = pending
    /\ terminated' = terminated
    /\ detected' = detected
  \/ \E i \in 1..N :
    /\ nodes[i] = <<TRUE, pending[i]>>
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
    /\ nodes' = nodes
    /\ terminated' = terminated
    /\ detected' = detected
  \/ \E i \in 1..N :
    /\ nodes[i] = <<TRUE, pending[i]>>
    /\ pending' = [pending EXCEPT ![i] = pending[i] + 1]
    /\ nodes' = nodes
    /\ terminated' = terminated
    /\ detected' = detected
  \/ DetectTermination

DetectTermination ==
  /\ \A i \in 1..N : nodes[i] = <<FALSE, 0>>
  /\ terminated' = TRUE
  /\ pending' = pending
  /\ nodes' = nodes
  /\ detected' = TRUE

Spec ==
  Init /\ [][Next]_<<nodes, pending, terminated, detected>>

TerminationImpliesDetection ==
  terminated => detected

TerminationStable ==
  []terminated => []terminated

ActualTerminationLeadsToDetection ==
  <>(terminated) => <>detected

Fairness ==
  WF_DetectTermination(DetectTermination)

THEOREM Spec => []TerminationImpliesDetection
THEOREM Spec => TerminationStable
THEOREM Spec => ActualTerminationLeadsToDetection
THEOREM Spec => Fairness
Inv == /\ terminated => detected
       /\ \A i \in 1..N : nodes[i] \in <<TRUE, 0>> .. <<FALSE, N>>
StateConstraint == \A i \in 1..N : pending[i] <= N

```
Note: This TLA+ specification is written based on the given description and might need adjustments according to specific requirements or additional constraints not mentioned.