```
MODULE TwoPhaseCommit
EXTENDS Integers, FiniteSets

CONSTANTS RMSet
VARIABLES rmState

Init ==
  /\ rmState \in [RMSet -> {"working"}]

Next ==
  \/ \E rm \in RMSet :
      /\ rmState[rm] = "working"
      /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  \/ \E rm \in RMSet :
      /\ rmState[rm] = "prepared"
      /\ (rmState' = [rmState EXCEPT ![rm] = "committed"]
       \/ rmState' = [rmState EXCEPT ![rm] = "aborted"])

Spec ==
  Init /\ [][Next]_rmState

TypeInvariant ==
  rmState \in [RMSet -> {"working", "prepared", "committed", "aborted"}]

ConsistencyInvariant ==
  \A rm1, rm2 \in RMSet :
    \/ rmState[rm1] = "working"
    \/ rmState[rm1] = "prepared"
    \/ rmState[rm1] = "aborted"
    \/ rmState[rm2] = "working"
    \/ rmState[rm2] = "prepared"
    \/ rmState[rm2] = "aborted"
    \/ /\ rmState[rm1] = "committed"
        /\ rmState[rm2] = "committed"

THEOREM Spec => []TypeInvariant
THEOREM Spec => []ConsistencyInvariant

Fairness ==
  WF_vars(Next, rmState)
```