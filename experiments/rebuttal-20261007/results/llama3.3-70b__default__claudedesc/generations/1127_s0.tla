```
MODULE TwoPhaseCommit
EXTENDS Integers, TLC

CONSTANTS RM

VARIABLES rmState

Init ==
  rmState = [r \in RM |-> "working"]

Prepare(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ \A x \in RM : rmState[x] \in {"prepared", "committed"}
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
  /\ r \in RM
  /\ rmState[r] \in {"working", "prepared"}
  /\ \A x \in RM : rmState[x] # "committed"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext ==
  \E r \in RM :
    Prepare(r)
    \/ DecideCommit(r)
    \/ DecideAbort(r)

Spec == Init /\ [][TCNext]_rmState

TCTypeOK ==
  \A r \in RM : rmState[r] \in {"working", "prepared", "committed", "aborted"}

TCConsistent ==
  ~\E r1, r2 \in RM :
    /\ rmState[r1] = "aborted"
    /\ rmState[r2] = "committed"

THEOREM Spec => []TCTypeOK
THEOREM Spec => []TCConsistent

```
Configuration for model checking:
```
CONSTANT RM <- {"r1", "r2", "r3"}
INVARIANT TCTypeOK
INVARIANT TCConsistent
```
Note: The `TLC` module is extended to use the TLC (Temporal Logic Checker) model checker. The `Integers` module is extended for integer operations, if needed.