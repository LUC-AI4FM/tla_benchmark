```
MODULE AtomicCommitProtocol

EXTENDS Integers, TLC

CONSTANTS RMSet
VARIABLES state

Init == (state = [i \in RMSet |-> "working"])

Next == 
  (\E i \in RMSet : 
    ((state[i] = "working") /\ (state' = [state EXCEPT ![i] = "prepared"]))
    \/ ((state[i] = "working") /\ (state' = [state EXCEPT ![i] = "aborted"]))
    \/ ((state[i] = "prepared") /\ (state' = [state EXCEPT ![i] = "committed"])
        /\ (\A j \in RMSet : state[j] = "prepared" \/ state[j] = "committed"))
    \/ ((state[i] = "prepared") /\ (state' = [state EXCEPT ![i] = "aborted"]))
  )

Spec == Init /\ [][Next]_

TypeCorrectness == \A i \in RMSet : state[i] \in {"working", "prepared", "committed", "aborted"}
Consistency == ~(\E i, j \in RMSet : state[i] = "committed" /\ state[j] = "aborted")

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []Consistency

RMSet <- {rm1, rm2, rm3}
```
Note: This TLA+ specification models the behavior of three resource managers (`rm1`, `rm2`, and `rm3`) using a single-phase atomic commit protocol. The `state` variable keeps track of each resource manager's state, which can be one of "working", "prepared", "committed", or "aborted". The `Next` action describes the possible state transitions for each resource manager. The `TypeCorrectness` and `Consistency` invariants ensure that every resource manager is always in a valid state and that no two resource managers ever reach conflicting decisions, respectively.