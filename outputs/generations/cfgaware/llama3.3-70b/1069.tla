---------------------------- MODULE AsyncTerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE nodes, pending, detected

Init ==
  /\ nodes = [i \in 1..N |-> <<TRUE, 0>>]
  /\ pending = [i \in 1..N |-> 0]
  /\ detected = FALSE

TypeInvariant ==
  /\ nodes \in [1..N -> {<<TRUE, 0>>, <<FALSE, 0>>} \cup {<<b, n> | b \in BOOLEAN, n \in Nat}]
  /\ pending \in [1..N -> Nat]
  /\ detected \in BOOLEAN

NodeTermination(i) ==
  /\ nodes[i] = <<TRUE, 0>>
  /\ nodes' = [nodes EXCEPT ![i] = <<FALSE, 0>>]
  /\ pending' = pending
  /\ detected' = detected

SendMessage(i) ==
  /\ nodes[i] = <<FALSE, 0>>
  /\ \E j \in 1..N : pending'[j] = pending[j] + 1
  /\ nodes' = nodes
  /\ detected' = detected

ReceiveMessage(i) ==
  /\ \E j \in 1..N : pending[j] > 0
  /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
  /\ nodes' = nodes
  /\ detected' = detected

DetectTermination ==
  /\ ~detected
  /\ \A i \in 1..N : nodes[i] = <<FALSE, 0>>
  /\ \A i \in 1..N : pending[i] = 0
  /\ detected' = TRUE
  /\ nodes' = nodes
  /\ pending' = pending

Next ==
  \/ \E i \in 1..N : NodeTermination(i)
  \/ \E i \in 1..N : SendMessage(i)
  \/ \E i \in 1..N : ReceiveMessage(i)
  \/ DetectTermination

Spec ==
  Init /\ [][Next]_<<nodes, pending, detected>>

THEOREM Spec => []detected => []~\E i \in 1..N : NodeTermination(i)

THEOREM Spec => []detected => <>DetectTermination

THEOREM Spec => WF_(DetectTermination) => []<>detected
=============================================================================