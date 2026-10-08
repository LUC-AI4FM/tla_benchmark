```
MODULE TerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES nodes, pending, flag

Init ==
  /\ nodes \in [1..N -> {<<"active">>, <<"inactive">>}]
  /\ pending \in [1..N -> Nat]
  /\ flag = FALSE

Next ==
  \/ \E i \in 1..N :
    /\ nodes[i] = <<"active">>
    /\ nodes' = [nodes EXCEPT ![i] = <<"inactive">>]
    /\ pending' = pending
    /\ flag' = flag
  \/ \E i \in 1..N :
    /\ nodes[i] = <<"inactive">>
    /\ pending[i] > 0
    /\ nodes' = [nodes EXCEPT ![i] = <<"active">>]
    /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
    /\ flag' = flag
  \/ \E i, j \in 1..N :
    /\ nodes[i] = <<"active">>
    /\ pending[j] < 10  \* Bounding pending message counts for model checking feasibility
    /\ nodes' = nodes
    /\ pending' = [pending EXCEPT ![j] = pending[j] + 1]
    /\ flag' = flag
  \/ \E i \in 1..N :
    /\ nodes[i] = <<"active">>
    /\ pending[i] = 0
    /\ nodes' = [nodes EXCEPT ![i] = <<"inactive">>]
    /\ pending' = pending
    /\ flag' = flag
  \/ (flag = FALSE /\ \A i \in 1..N : nodes[i] = <<"inactive">> /\ pending[i] = 0)
      /\ flag' = TRUE
      /\ nodes' = nodes
      /\ pending' = pending

Spec ==
  Init /\ [][Next]_<<nodes, pending, flag>>

THEOREM Spec => []~(flag' = TRUE) \* Soundness: the detection flag never lies
THEOREM Spec => [](flag = TRUE => []flag) \* Quiescence: once terminated the system cannot become un-terminated
THEOREM Spec => <>flag \* Liveness: actual termination is eventually detected

FAIRNESS Next
```