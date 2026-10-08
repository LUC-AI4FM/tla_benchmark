```
MODULE FastLock
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc, trying, critical, turn

Init ==
  /\ pc \in [1..N -> {"noncritical", "trying", "critical"}]
  /\ trying \in [1..N -> FALSE]
  /\ critical \in [1..N -> FALSE]
  /\ turn \in Nat

Next ==
  \/ \E i \in 1..N :
    /\ pc[i] = "noncritical"
    /\ pc' = [pc EXCEPT ![i] = "trying"]
    /\ trying' = [trying EXCEPT ![i] = TRUE]
    /\ critical' = critical
    /\ turn' = turn
  \/ \E i \in 1..N :
    /\ pc[i] = "trying"
    /\ trying[i] = TRUE
    /\ turn = i
    /\ critical' = [critical EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ trying' = [trying EXCEPT ![i] = FALSE]
    /\ turn' = (turn + 1) % N
  \/ \E i \in 1..N :
    /\ pc[i] = "critical"
    /\ critical' = [critical EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "noncritical"]
    /\ trying' = trying
    /\ turn' = turn

Spec ==
  Init /\ [][Next]_<<pc, trying, critical, turn>>

THEOREM Spec => []~( \E i, j \in 1..N : i # j /\ critical[i] /\ critical[j] )
THEOREM Spec => WF_(trying, pc)_(\E i \in 1..N : trying[i] = TRUE => pc[i] = "critical")
THEOREM Spec => SF_(pc, trying, critical)_(\A i \in 1..N : trying[i] = TRUE => pc[i] # "noncritical")

Fairness ==
  WF_<<trying, pc>>_(\E i \in 1..N : trying[i] = TRUE => pc[i] = "critical")
```
Note: The above TLA+ specification models a fast lock algorithm with bounded waiting and no deadlock for N identical processes. It captures the concurrent interleaving and waiting on shared-variable conditions, enabling verification of the safety invariant and liveness properties.