```tla
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES nodes, pending, detected

Init == (
  /\ nodes \in [1..N -> {active, inactive}]
  /\ pending \in [1..N -> Nat]
  /\ detected = FALSE
)

Next == (
  /\ (\/ \exists i \in 1..N : 
      /\ nodes[i] = active
      /\ nodes' = [nodes EXCEPT ![i] = inactive]
      /\ pending' = pending
      /\ detected' = detected
    \/ \exists i \in 1..N :
      /\ pending[i] > 0
      /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
      /\ nodes' = nodes
      /\ detected' = detected
    \/ \exists i \in 1..N :
      /\ pending[i] < N
      /\ pending' = [pending EXCEPT ![i] = pending[i] + 1]
      /\ nodes' = nodes
      /\ detected' = detected
    \/ (\/ \forall i \in 1..N : 
          /\ nodes[i] = inactive
          /\ pending[i] = 0
        )
        /\ detected' = TRUE
        /\ nodes' = nodes
        /\ pending' = pending
    )
  /\ (detected' => detected)
)

Spec == Init /\ [][Next]_<<nodes, pending, detected>>
Inv == (
  /\ detected => \forall i \in 1..N : nodes[i] = inactive
  /\ detected => \forall i \in 1..N : pending[i] = 0
)

TerminationImpliesDetection == []<>(detected)
DetectionStable == []~detected => []detected

FairnessDetectTermination == SF_VARIABLES(DetectTermination)
DetectTermination == (
  /\ (\/ \forall i \in 1..N :
      /\ nodes[i] = inactive
      /\ pending[i] = 0
    )
  /\ detected' = TRUE
  /\ nodes' = nodes
  /\ pending' = pending
)

THEOREM Spec => []Inv
THEOREM Spec => TerminationImpliesDetection
THEOREM Spec => DetectionStable
THEOREM Spec => FairnessDetectTermination => TerminationImpliesDetection

StateConstraint == (
  /\ Cardinality(nodes) <= N
  /\ \forall i \in 1..N : nodes[i] \in {active, inactive}
  /\ \forall i \in 1..N : pending[i] >= 0
)
```