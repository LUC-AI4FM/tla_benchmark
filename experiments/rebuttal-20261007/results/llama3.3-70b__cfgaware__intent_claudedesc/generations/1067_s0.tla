---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE nodes, detected

Init ==
  /\ nodes \in [1..N -> {<<"active">>, <<"inactive">>}]
  /\ detected = (nodes = [i \in 1..N |-> <<"inactive">>])

Next ==
  \/ \E i \in 1..N :
      /\ nodes[i] = <<"active">>
      /\ nodes' = [nodes EXCEPT ![i] = <<"inactive">>]
      /\ detected' = detected
  \/ \E i \in 1..N :
      /\ nodes[i] = <<"active">>
      /\ \E j \in 1..N :
          /\ nodes[j] = <<"inactive">>
          /\ nodes' = [nodes EXCEPT ![j] = <<"active">>]
          /\ detected' = detected
  \/ detected = FALSE
    /\ nodes = [i \in 1..N |-> <<"inactive">>]
    /\ detected' = TRUE
    /\ nodes' = nodes

Spec ==
  Init /\ [][Next]_<<nodes, detected>>
  WF_(detected = FALSE, detected' = TRUE)_<<nodes, detected>>

THEOREM Spec => []~(detected = TRUE /\ \E i \in 1..N : nodes[i] = <<"active">>)
THEOREM Spec => []((\A i \in 1..N : nodes[i] = <<"inactive">>) => []( \A j \in 1..N : nodes[j] = <<"inactive">>))
THEOREM Spec => <>[]detected = TRUE
=============================================================================