------------------------------ MODULE TwoPhaseCommit ------------------------------

EXTENDS Naturals

CONSTANT RM

VARIABLE rmState

States == {"working", "prepared", "committed", "aborted"}

Init ==
  rmState = [r \in RM |-> "working"]

RMsIn(s) == { r \in RM : rmState[r] = s }

ExistsCommitted == \E r \in RM: rmState[r] = "committed"
ExistsAborted  == \E r \in RM: rmState[r] = "aborted"

AllPreparedOrCommitted ==
  \A r \in RM: rmState[r] \in {"prepared", "committed"}

CanCommit == /\ ~ExistsAborted
             /\ AllPreparedOrCommitted

Prepare(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ CanCommit
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
  /\ r \in RM
  /\ rmState[r] \in {"working", "prepared"}
  /\ ~ExistsCommitted
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) ==
  DecideCommit(r) \/ DecideAbort(r)

Next ==
  \E r \in RM:
    Prepare(r) \/ Decide(r)

Spec ==
  Init /\ [][Next]_rmState

TypeOK ==
  rmState \in [RM -> States]

ConsistentDecision ==
  ~(\E r1, r2 \in RM:
      /\ rmState[r1] = "committed"
      /\ rmState[r2] = "aborted")

THEOREM Spec => []TypeOK
THEOREM Spec => []ConsistentDecision

=============================================================================