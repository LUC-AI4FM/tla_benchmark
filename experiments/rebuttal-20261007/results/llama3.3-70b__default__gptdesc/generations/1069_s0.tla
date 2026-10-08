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
  \/ \E i \in 1..N :
    /\ nodes[i] = active
    /\ nodes' = [nodes EXCEPT ![i] = inactive]
    /\ pending' = pending
    /\ detected' = detected
  \/ \E i \in 1..N :
    /\ nodes[i] = active
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
    /\ nodes' = nodes
    /\ detected' = detected
  \/ \E i \in 1..N :
    /\ nodes[i] = active
    /\ pending[i] < N
    /\ pending' = [pending EXCEPT ![i] = pending[i] + 1]
    /\ nodes' = nodes
    /\ detected' = detected
  \/ DetectTermination

DetectTermination ==
  /\ \A i \in 1..N : nodes[i] = inactive
  /\ \A i \in 1..N : pending[i] = 0
  /\ detected' = TRUE
  /\ nodes' = nodes
  /\ pending' = pending

Spec == Init /\ [][Next]_<<nodes, pending, detected>>
          /\ WF_(DetectTermination)_(nodes, pending, detected)

TerminationImpliesDetection ==
  \A i \in 1..N : nodes[i] = inactive => detected

TerminationStable ==
  detected => detected'

ActualTerminationLeadsToDetection ==
  <>(\A i \in 1..N : nodes[i] = inactive /\ \A i \in 1..N : pending[i] = 0) => <>detected

TypeInvariant == 
  /\ nodes \in [1..N -> {active, inactive}]
  /\ pending \in [1..N -> Nat]
  /\ detected \in BOOLEAN
```