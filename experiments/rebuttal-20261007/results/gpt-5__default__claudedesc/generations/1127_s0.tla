---- MODULE TwoPhaseCommit ----
EXTENDS Naturals

CONSTANT RM

VARIABLE rmState

States == {"working", "prepared", "committed", "aborted"}

Init ==
  rmState = [r \in RM |-> "working"]

AllPreparedOrCommitted ==
  \A r \in RM : rmState[r] \in {"prepared", "committed"}

NoneCommitted ==
  \A r \in RM : rmState[r] # "committed"

Prepare(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ AllPreparedOrCommitted
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
  /\ r \in RM
  /\ rmState[r] \in {"working", "prepared"}
  /\ NoneCommitted
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Next ==
  \E r \in RM :
    Prepare(r) \/ DecideCommit(r) \/ DecideAbort(r)

Spec ==
  Init /\ [][Next]_rmState

TCTypeOK ==
  rmState \in [RM -> States]

TCConsistent ==
  ~(\E r1, r2 \in RM : rmState[r1] = "aborted" /\ rmState[r2] = "committed")
====