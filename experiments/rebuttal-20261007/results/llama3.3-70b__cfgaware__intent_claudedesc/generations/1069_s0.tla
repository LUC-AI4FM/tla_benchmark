---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE nodes, pending, detectionFlag

Init ==
  /\ nodes \in [1..N -> {<<"active">>, <<"inactive">>}]
  /\ pending = [i \in 1..N |-> 0]
  /\ detectionFlag = (nodes = [i \in 1..N |-> <<"inactive">>])

Next ==
  \/ \E i \in 1..N :
    /\ nodes[i] = <<"active">>
    /\ nodes' = [nodes EXCEPT ![i] = <<"inactive">>]
    /\ pending' = pending
    /\ detectionFlag' = detectionFlag
  \/ \E i \in 1..N :
    /\ nodes[i] = <<"active">>
    /\ \E j \in 1..N :
      /\ pending' = [pending EXCEPT ![j] = @ + 1]
      /\ nodes' = [nodes EXCEPT ![j] = <<"active">>]
      /\ detectionFlag' = detectionFlag
  \/ \E i \in 1..N :
    /\ pending[i] > 0
    /\ nodes' = [nodes EXCEPT ![i] = <<"active">>]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ detectionFlag' = detectionFlag
  \/ /\ nodes = [i \in 1..N |-> <<"inactive">>]
     /\ pending = [i \in 1..N |-> 0]
     /\ detectionFlag' = TRUE
     /\ nodes' = nodes
     /\ pending' = pending

Terminated ==
  /\ nodes = [i \in 1..N |-> <<"inactive">>]
  /\ pending = [i \in 1..N |-> 0]

Spec == Init /\ [][Next]_<<nodes, pending, detectionFlag>>

THEOREM Spec => []~<>(detectionFlag = TRUE) => []Terminated
THEOREM Spec => <>Terminated => <>(detectionFlag = TRUE)
=============================================================================